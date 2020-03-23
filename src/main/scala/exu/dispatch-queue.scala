package boom.exu

import chisel3._
import chisel3.util._
import freechips.rocketchip.config.Parameters
import boom.common.{IQT_MFP, MicroOp, O3PIPEVIEW_PRINTF, uopLD, _}
import boom.util._
import chisel3.internal.naming.chiselName
import freechips.rocketchip.util.DescribedSRAM

case class DispatchQueueParams(
                                val numEntries: Int,
                                val deqWidth: Int,
                                val enqWidth: Int,
                                val qName: String
                      )

class DispatchQueueIO(
                       val deqWidth: Int = 1,
                       val enqWidth: Int = 2)
                     (implicit p: Parameters) extends BoomBundle {
  val enq_uops = Vec(enqWidth, Flipped(DecoupledIO(new MicroOp)))
  val heads = Vec(deqWidth, DecoupledIO(new MicroOp()))
  val brinfo = Input(new BrResolutionInfo())
  val flush = Input(new Bool)
  val tsc_reg = Input(UInt(width=xLen.W)) // needed for pipeview
}



abstract class DispatchQueue( val numEntries: Int = 8,
                              val deqWidth: Int = 1,
                              val enqWidth: Int = 2,
                              val qName: String
                            )(implicit p: Parameters) extends BoomModule
{
  val io = IO(new DispatchQueueIO(deqWidth, enqWidth))
  val qAddrSz: Int = log2Ceil(numEntries)

  // Maps i to idx of queue. Used with for-loops starting at head or tail
  def wrapIndex(i: UInt): UInt = {
    val out = Wire(UInt(qAddrSz.W))
    when(i <= numEntries.U) {
      out := i
    }.otherwise {
      out := i - numEntries.U
    }
    out
  }
}

class SramDispatchQueue (params: DispatchQueueParams,
                        )(implicit p: Parameters) extends DispatchQueue(params.numEntries, params.deqWidth, params.enqWidth, params.qName)
{
  // enqWidth has to be bigger than deqWidth
  require(enqWidth >= deqWidth)

  val sram_fifo = (0 until enqWidth).map(i => SyncReadMem(numEntries, new MicroOp))

  // Branch mask and valid bits are still stored in Regs
  val br_mask = Reg(Vec(numEntries, Vec(enqWidth,UInt(maxBrCount.W) )))
  val valids = RegInit(VecInit(Seq.fill(numEntries)(VecInit(Seq.fill(enqWidth)(false.B)))))
  val head = RegInit(0.U(qAddrSz.W))
  val tail = RegInit(0.U(qAddrSz.W))
  val full = WireInit(false.B)
  val empty = WireInit(true.B)

  // Deqeueue pointer maps dequeue port (io.heads) to FIFO-lane.
  val deq_ptr = WireInit(VecInit(Seq.fill(enqWidth)(0.U(log2Ceil(deqWidth).W))))

  // Stage 1 enqueues stored for bypassing.
  val s1_enq_uops = Reg(Vec(enqWidth, new MicroOp()))
  val s1_enq_valids = Reg(Vec(enqWidth, Bool()))
  val s1_bypass = RegInit(false.B)

  // Stage 2 read-outs from SRAM
  val s2_sram_read = Wire(Vec(enqWidth, new MicroOp()))


  // Wires for calculating state in next CC
  val head_next = WireInit(head) // needs to be initialized here because firrtl can't detect that an assignment condition is always met
  val tail_next = Wire(UInt(qAddrSz.W))

  // Wires for branch resolutions
  val updated_brmask = WireInit(VecInit(Seq.fill(numEntries)(VecInit(Seq.fill(enqWidth)(false.B))))) //This wire decides if we should block the deque from head because of a branch resolution
  val entry_killed = WireInit(VecInit(Seq.fill(numEntries)(VecInit(Seq.fill(enqWidth)(false.B)))))


  // Handle enqueues
  for (w <- 0 until enqWidth) {
    when(io.enq_uops(w).fire) {
      sram_fifo(w)(tail) := WireInit(io.enq_uops(w).bits) //TODO: WireInit necessary?
      valids(tail)(w) := io.enq_uops(w).valid
      br_mask(tail)(w) := io.enq_uops(w).bits.br_mask

      // Here we assume that we dont try to enqueue anything to a full queue
      assert(!valids(tail)(w), "[dis-q] tyring to enqueue to a full queue")
    }
    // Latch this for potential bypass
    s1_enq_uops(w) := io.enq_uops(w).bits
    s1_enq_valids(w) := io.enq_uops(w).valid
  }

  s1_bypass := empty && io.enq_uops.map(_.valid).reduce(_||_) //Bypass next CC if we enqueue to an empty FIFO

  // Update tail
  //  We only update the tail for the next CC if there was a fire
  tail_next := Mux(io.enq_uops.map(_.fire).reduce(_ || _), WrapInc(tail,numEntries), tail)

  // Read from SRAM
  for(i <- 0 until enqWidth) {
    s2_sram_read(i) := sram_fifo(i)(head_next)
  }

  // Pass out the head
  //  Init all outputs to invalids
  //  A little hacking to assign a possible wider set of FIFOs to a narrower set of deq ports
  io.heads.map(_.valid := false.B)
  io.heads.map(_.bits := DontCare) //TODO: Connect to NOP?
  val deqPortUsed = WireInit(VecInit(Seq.fill(enqWidth)(false.B)))
  for(i <- 0 until enqWidth) {
    val idx = Wire(UInt(log2Ceil(enqWidth).W))
    if(i == 0) {
      idx := 0.U
    }
    else {
      idx := PopCount(deqPortUsed.slice(0,i))
    }

    when(valids(head)(i) && idx < deqWidth.U) {
      io.heads(idx).valid :=  valids(head)(i) &&
                              !entry_killed(head)(i) &&
                              !io.flush

      when(s1_bypass) {

        io.heads(idx).bits := s1_enq_uops(i)
        // If we have a branch resolution this CC we need to update the bypassed instruction as well
        io.heads(idx).bits.br_mask := Mux(updated_brmask(head)(i), br_mask(head)(i) & ~io.brinfo.mask, br_mask(head)(i))


      }.otherwise {
        io.heads(idx).bits := s2_sram_read(i)
        // If we have a branch resolution this cycle. Be sure to pass out the updated Brmask and not the old
        //  TODO: Can this affect the Critical Path?
        io.heads(idx).bits.br_mask := Mux(updated_brmask(head)(i), br_mask(head)(i) & ~io.brinfo.mask, br_mask(head)(i))

      }

      deqPortUsed(i) := true.B
      deq_ptr(idx) := i.U
    }
  }



  // Handle dequeues
  for (i <- 0 until deqWidth) {
    when(io.heads(i).fire) {
      valids(head)(deq_ptr(i)) := false.B
      assert(valids(head)(deq_ptr(i)), "[dis-q] Dequeued invalid uop from head")
      assert(!entry_killed(head)(deq_ptr(i)), "[dis-q] Dequeued killed uop from head")
    }
  }

  // Calculate next head
  when(valids(head).reduce(_ || _)) {
    // Case 1: We entered this CC with some valid uops at head
    //  Either those were dequeded this CC and we move head_pointer or w stay at this head
    //  This double loop is a clonky way of checking it. It checks wether all of the valids at head
    //  also match the ones dequeued this CC
    val proceed = WireInit(true.B)
    for (i <- 0 until enqWidth) {
      val uop_done = WireInit(false.B)
      for(j <- 0 until deqWidth) {
        when(!valids(head)(i) || (io.heads(j).fire && deq_ptr(j) === i.U )) {
          uop_done := true.B
        }
      }
      when(!uop_done) {
        proceed := false.B
      }
    }
    head_next := Mux(proceed, WrapInc(head, numEntries), head)
  }



  // Handle branch resolution
  //  On mispredict, find oldest that is killed and kill everyone younger than that
  //  On resolved. Update all branch masks in paralell. Updates also invalid entries, for simplicity.
  //
  // This function takes a killed and valid Vec and finds out of the whole Vec was killed or is invalid
  def width_killed(k: Vec[Bool], v: Vec[Bool]): Bool = {
    v.reduce(_ || _ ) && (k zip v).map{case (kill, valid) => kill || !valid}.reduce(_&&_)
  }
  when(io.brinfo.valid) {
    for (idx <- 0 until numEntries) {
      for(lane <- 0 until enqWidth) {
        val entry_match = valids(idx)(lane) && maskMatch(io.brinfo.mask, br_mask(idx)(lane))
        when (entry_match && io.brinfo.mispredict) { // Mispredict
          entry_killed(idx)(lane) := true.B
          valids(idx)(lane) := false.B
        }.elsewhen(entry_match && !io.brinfo.mispredict) { // Resolved
          br_mask(idx)(lane) := (br_mask(idx)(lane) & ~io.brinfo.mask)
          updated_brmask(idx)(lane) := true.B
        }
      }
    }


    // tail update logic
    for (i <- 0 until numEntries) {
      // treat it as a circular structure
      val previous_killed =
      if (i == 0) {
        width_killed(entry_killed(numEntries - 1) ,valids(numEntries - 1))
      } else {
        width_killed(entry_killed(i-1) ,valids(i-1))
      }
      val this_killed = width_killed(entry_killed(i) ,valids(i))

      // transition from not killed to killed - there should be one at maximum
      when(!previous_killed && this_killed){
        // this one was killed but the previous one not => this is tail
        // if branches are killed there should be nothing being enqueued
        // TODO: make sure this is true (assert)
        tail_next := i.U
      }
    }
  }

  assert(! (io.brinfo.mispredict && io.brinfo.valid &&  width_killed(entry_killed(head), valids(head)) && (head_next =/= tail_next)), "[dis-q] branch resolution with head flushed but head and tail_next not reset")
  assert(! (RegNext(io.brinfo.mispredict && io.brinfo.valid && width_killed(entry_killed(head), valids(head))) && (full =/= false.B || empty =/= true.B )), "[dis-q] branch resolution with head flushed but empty, full not reset")




  require(enqWidth>=coreWidth)


  for (w <- 0 until enqWidth)
  {
    io.enq_uops(w).ready := !full
  }


  // Full/Empty
  when(head === tail) {
    full := true.B
    empty := false.B
    for (i <- 0 until numEntries) {
      when(!valids(i).reduce(_||_)) {
        full := false.B
        empty := true.B
      }
    }
  }.otherwise {
    full := false.B
    empty := false.B
  }

  // Pipeline flushs
  when(io.flush)
  {
    head_next := 0.U
    tail_next := 0.U
    valids.map(_.map(_ := false.B))
    }

  // Update for next CC
  head := head_next
  tail := tail_next

  if (O3PIPEVIEW_PRINTF) {
    for (i <- 0 until coreWidth) {
      when (io.enq_uops(i).valid) {
        printf("%d; O3PipeView:"+qName+": %d\n",
          io.enq_uops(i).bits.debug_events.fetch_seq,
          io.tsc_reg)
      }
    }
  }

  dontTouch(io)
  dontTouch(valids)
  dontTouch(head)
  dontTouch(tail)
  dontTouch(head_next)
  dontTouch(tail_next)
  dontTouch(full)
  dontTouch(empty)
}



@chiselName
class SliceDispatchQueue(params: DispatchQueueParams,
                        )(implicit p: Parameters) extends DispatchQueue(params.numEntries, params.deqWidth, params.enqWidth, params.qName)
  {


  // Queue state
  val q_uop = Reg(Vec(numEntries, new MicroOp()))
  val valids = RegInit(VecInit(Seq.fill(numEntries)(false.B)))
  val head = RegInit(0.U(qAddrSz.W))
  val tail = RegInit(0.U(qAddrSz.W))


  // Wires for calculating state in next CC
  val head_next = WireInit(head) // needs to be initialized here because firrtl can't detect that an assignment condition is always met
  val tail_next = Wire(UInt(qAddrSz.W))

  // Handle enqueues
  //  Use WrapInc to sequentialize an arbitrary number of enqueues.
  val enq_idx = Wire(Vec(coreWidth, UInt(qAddrSz.W)))
  for (w <- 0 until coreWidth) {
    if (w == 0) {
      enq_idx(w) := tail
    } else {
      // Here we calculate the q idx to pass back to the ROB
      enq_idx(w) := Mux(io.enq_uops(w - 1).fire, WrapInc(enq_idx(w - 1), numEntries), enq_idx(w - 1))
    }

    when(io.enq_uops(w).fire)
    {
      valids(enq_idx(w)) := true.B
      q_uop(enq_idx(w)) := io.enq_uops(w).bits
    }
  }
  // Update tail
  //  We have already incremented the tail pointer in the previous loop.
  //  Only needs a last increment if the last enq port also fired
  tail_next := Mux(io.enq_uops(coreWidth - 1).fire, WrapInc(enq_idx(coreWidth - 1), numEntries), enq_idx(coreWidth - 1))

  // Handle dequeues
  // on more so we also do something if all are dequeued
  for (i <- 0 until deqWidth+1) {
    val previous_deq = if(i==0) true.B else io.heads(i-1).fire()
    val current_deq =  if(i==deqWidth) false.B else io.heads(i).fire()
    assert(!(boomParams.loadSliceMode.asBool && !previous_deq && current_deq), "deq only possible in order!")
    // transition from deq to not deq - there should be exactly one
    // TODO: maybe do this in a smarter way so the compiler knows this and can optimize?
    when(previous_deq && !current_deq){
      // TODO: something other than % for wrap?
      head_next := (head+i.U)%numEntries.U
    }
  }


  // Handle branch resolution
  //  On mispredict, find oldest that is killed and kill everyone younger than that
  //  On resolved. Update all branch masks in paralell. Updates also invalid entries, for simplicity.
  val updated_brmask = WireInit(false.B)//VecInit(Seq.fill(numEntries)(false.B))) //This wire decides if we should block the deque from head because of a branch resolution
val entry_killed = WireInit(VecInit(Seq.fill(numEntries)(false.B)))
  when(io.brinfo.valid) {
    for (i <- 0 until numEntries) {
      val br_mask = q_uop(i).br_mask
      val entry_match = valids(i) && maskMatch(io.brinfo.mask, br_mask)

      when (entry_match && io.brinfo.mispredict) { // Mispredict
        entry_killed(i) := true.B
        valids(i) := false.B
      }.elsewhen(entry_match && !io.brinfo.mispredict) { // Resolved
        q_uop(i).br_mask := (br_mask & ~io.brinfo.mask)
        updated_brmask := true.B
      }
    }
    // tail update logic
    for (i <- 0 until numEntries) {
      // treat it as a circular structure
      val previous_killed = if(i==0) entry_killed(numEntries-1) else entry_killed(i-1)
      // transition from not killed to killed - there should be one at maximum
      when(!previous_killed && entry_killed(i)){
        // this one was killed but the previous one not => this is tail
        // if branches are killed there should be nothing being enqueued
        // TODO: make sure this is true (assert)
        tail_next := i.U
      }
    }
  }


  // Pipeline flushs
  when(io.flush)
  {
    head_next := 0.U
    tail_next := 0.U
    valids.map(_ := false.B)
  }

  require(numEntries>2*coreWidth)


  for(i <- 0 until deqWidth){
    for(i <- 0 until deqWidth){
      val idx = head + i.U
      // Route out IO
      io.heads(i).bits := q_uop(idx)
      io.heads(i).valid :=  valids(idx) &&
        !updated_brmask && //TODO: this might lead to poor performance
        !entry_killed(idx) &&
        !io.flush // TODO: handle flush?
      when(io.heads(i).fire()){
        valids(idx) := false.B
      }
    }
  }

  for (w <- 0 until coreWidth)
  {
    io.enq_uops(w).ready := !valids(tail+w.U) //TODO: ensure it is possible to take only some from rename
  }

  // Update for next CC
  head := head_next
  tail := tail_next

  // TODO: update
  //  // dequeue implies queue valid (not empty)
  //  assert(!io.deq_uop || !empty)
  //
  //  // empty implies ready
  //  assert(!empty || ready)
  //
  //  // enqueue implies ready
  //  assert(!io.enq_uops.map(_.valid).reduce(_||_) || ready)
  //
  //  // No deques on flush
  //  assert(!(io.deq_uop && io.flush))

  if (O3PIPEVIEW_PRINTF) {
    for (i <- 0 until coreWidth) {
      when (io.enq_uops(i).valid) {
        printf("%d; O3PipeView:"+qName+": %d\n",
          io.enq_uops(i).bits.debug_events.fetch_seq,
          io.tsc_reg)
      }
    }
  }

  dontTouch(io)
  dontTouch(q_uop)
  dontTouch(valids)
  dontTouch(head)
  dontTouch(tail)
  dontTouch(head_next)
  dontTouch(tail_next)
}
