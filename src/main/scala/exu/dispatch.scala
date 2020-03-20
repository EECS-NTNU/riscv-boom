//******************************************************************************
// Copyright (c) 2012 - 2019, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE and LICENSE.SiFive for license details.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// BOOM Instruction Dispatcher
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------


package boom.exu

import chisel3._
import chisel3.util._
import freechips.rocketchip.config.Parameters
import boom.common.{IQT_MFP, MicroOp, O3PIPEVIEW_PRINTF, uopLD, _}
import boom.util._
import chisel3.internal.naming.chiselName


class DispatchIO(implicit p: Parameters) extends BoomBundle
{
  // incoming microops from rename2
  val ren_uops = Vec(coreWidth, Flipped(DecoupledIO(new MicroOp)))

  // outgoing microops to issue queues
  // N issues each accept up to dispatchWidth uops
  // dispatchWidth may vary between issue queues
  val dis_uops = MixedVec(issueParams.map(ip=>Vec(ip.dispatchWidth, DecoupledIO(new MicroOp))))
  // io for busy table - used only for LSC
  val busy_req_uops = if(boomParams.busyLookupMode) Some(Output(Vec(boomParams.busyLookupParams.get.lookupAtDisWidth, new MicroOp))) else None //TODO: change width
  val busy_resps = if(boomParams.busyLookupMode) Some(Input(Vec(boomParams.busyLookupParams.get.lookupAtDisWidth, new BusyResp))) else None
  val fp_busy_req_uops = if(boomParams.busyLookupMode && usingFPU) Some(Output(Vec(boomParams.busyLookupParams.get.lookupAtDisWidth, new MicroOp))) else None
  val fp_busy_resps = if(boomParams.busyLookupMode && usingFPU) Some(Input(Vec(boomParams.busyLookupParams.get.lookupAtDisWidth, new BusyResp))) else None
  // brinfo & flush for LSC
  val brinfo = if(boomParams.loadSliceMode || boomParams.dnbMode) Some(Input(new BrResolutionInfo())) else None
  val flush = if(boomParams.loadSliceMode || boomParams.dnbMode) Some(Input(Bool())) else None

  // DnB ports to UIQ
  val dlq_head = if(boomParams.dnbMode) Some(DecoupledIO(new MicroOp)) else None
  val crq_head = if(boomParams.dnbMode) Some(DecoupledIO(new MicroOp)) else None

  val tsc_reg = Input(UInt(width=xLen.W))

  val lsc_perf = if(boomParams.loadSliceMode) Some(Output(new LscDispatchPerfCounters)) else None
  val dnb_perf = if(boomParams.dnbMode) Some(Output(new DnbDispatchPerfCounters)) else None
}


/**
  *
  * Performance counters for LSC
  */


class LscDispatchPerfCounters(implicit p: Parameters) extends BoomBundle {
  val aq = Vec(decodeWidth, Bool()) // Number of insts in A-Q
  val bq = Vec(decodeWidth, Bool()) // Number of insts on B-Q
}

class DnbDispatchPerfCounters(implicit p: Parameters) extends BoomBundle {
  val dlq = Vec(decodeWidth, Bool()) // Number of insts in DLQ
  val crq = Vec(decodeWidth, Bool()) // Number of insts on CRQ
  val iq = Vec(decodeWidth, Bool()) // Number of insts on IQ
}


abstract class Dispatcher(implicit p: Parameters) extends BoomModule
{
  val io = IO(new DispatchIO)
}

/**
 * This Dispatcher assumes worst case, all dispatched uops go to 1 issue queue
 * This is equivalent to BOOMv2 behavior
 */
class BasicDispatcher(implicit p: Parameters) extends Dispatcher
{
  issueParams.map(ip=>require(ip.dispatchWidth == coreWidth))

  val ren_readys = io.dis_uops.map(d=>VecInit(d.map(_.ready)).asUInt).reduce(_&_)

  for (w <- 0 until coreWidth) {
    io.ren_uops(w).ready := ren_readys(w)
  }

  for {i <- 0 until issueParams.size
       w <- 0 until coreWidth} {
    val issueParam = issueParams(i)
    val dis        = io.dis_uops(i)

    dis(w).valid := io.ren_uops(w).valid && ((io.ren_uops(w).bits.iq_type & issueParam.iqType.U) =/= 0.U)
    dis(w).bits  := io.ren_uops(w).bits
  }
}

@chiselName
class DnbDispatcher(implicit p: Parameters) extends Dispatcher {
  // FIFOs
  val dnbParams = boomParams.dnbParams.get
  val dlq = Module(new SliceDispatchQueue( DispatchQueueParams(
    numEntries = dnbParams.numDlqEntries,
    qName="DLQ",
    deqWidth=1,
    enqWidth= coreWidth)))


  val crq = Module(new SliceDispatchQueue( DispatchQueueParams(
    numEntries = dnbParams.numCrqEntries,
    qName="CRQ",
    deqWidth=1,
    enqWidth = coreWidth)))

  // Route brinfo and flush into the fifos
  dlq.io.brinfo := io.brinfo.get
  dlq.io.flush := io.flush.get
  crq.io.brinfo := io.brinfo.get
  crq.io.flush  := io.flush.get

  // Route in tsc for pipeview
  dlq.io.tsc_reg := io.tsc_reg
  crq.io.tsc_reg := io.tsc_reg

  // Initialize the perf counters
  io.dnb_perf.get.dlq.map(_ := false.B)
  io.dnb_perf.get.crq.map(_ := false.B)
  io.dnb_perf.get.iq.map(_ := false.B)


  val dis_stall = WireInit(VecInit(Seq.fill(coreWidth)(false.B)))
  var previous_ready = true.B
  for (i <- 0 until coreWidth) {
    // Just get uop bits, valid and critical/busy info
    val uop = io.ren_uops(i).bits
    val uop_critical = uop.is_lsc_b
    val uop_iq = uop.uopc === uopLD || uop.uopc === uopSTA || uop.uopc === uopSTD //TODO: FP STW?
    val uop_busy = (uop.prs1_busy || uop.prs2_busy || uop.prs3_busy)

    // Check if this uop must be split into 2 which creates some extra corner cases
    val uop_split = uop.uopc === uopSTA

    // Initialize the ports to false and just add the uop
    dlq.io.enq_uops(i).bits := uop
    dlq.io.enq_uops(i).valid := false.B
    io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).bits := uop
    io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).valid := false.B
    crq.io.enq_uops(i).bits := uop
    crq.io.enq_uops(i).valid := false.B

    //ready logic - only ready if all lower rename ports and all possible target ports are ready
    io.ren_uops(i).ready := previous_ready &&
      dlq.io.enq_uops(i).ready &&
      io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).ready &&
      crq.io.enq_uops(i).ready
    previous_ready = io.ren_uops(i).ready

    when(io.ren_uops(i).fire()) {
      when(!uop_split) {
        // Normal non-splitting case
        // Based on critical/busy which FIFO/IQ do we wanna use?
        when(!uop_critical && !uop_iq) {
          //dlq
          dlq.io.enq_uops(i).valid := true.B
          io.dnb_perf.get.dlq(i) := true.B
        }.otherwise {
          when(uop_busy || uop_iq) {
            //iq
            io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).valid := true.B
            io.dnb_perf.get.iq(i) := true.B

          }.otherwise {
            //crq
            crq.io.enq_uops(i).valid := true.B
            io.dnb_perf.get.crq(i) := true.B
          }
        }
      }.otherwise { // Uop splitting case
        // Currently 2 cases. STORE and FP STORE. We want the uopSTD to go in the DLQ and the uopSTA on the IQ
        //  If we dont have place for both, i.e. in DLQ and IQ we will stall
        val uop_sta = WireInit(uop)
        val uop_std = WireInit(uop)

        // address
        uop_sta.lrs2_rtype := RT_X
        uop_sta.prs2_busy := false.B
        // data
        uop_std.lrs1_rtype := RT_X
        uop_std.prs1_busy := false.B

        when(uop.iq_type === IQT_MEM) {
          // INT stores
          uop_sta.uopc := uopSTA
          uop_std.uopc := uopSTD
        }.otherwise {
          // FP stores
          uop_sta.uopc := uopSTA
          uop_sta.iq_type := IQT_MEM
          uop_std.iq_type := IQT_FP
        }
        io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).valid := true.B
        io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).bits := uop_sta

        dlq.io.enq_uops(i).valid := true.B
        dlq.io.enq_uops(i).bits := uop_std

        io.dnb_perf.get.dlq(i) := true.B
        io.dnb_perf.get.iq(i) := true.B
      }
    }
  }

  if(O3PIPEVIEW_PRINTF){ // dispatch is here because it only happens for IQ and not dlq/crq
    io.dis_uops(LSC_DIS_COMB_PORT_IDX).foreach( port =>{
      when (port.fire()) {
        printf("%d; O3PipeView:dispatch: %d\n", port.bits.debug_events.fetch_seq, io.tsc_reg)
      }
    })
  }

  // Handle CRQ dequeues
  io.crq_head.get <> crq.io.heads(0)

  // Handle DLQ dequeues
  //  A little more complicated as we need to pass along the updated ready info
  //  Connect uop to both FP and INT busy table. Pick the resp based on the lrs-types
  io.busy_req_uops.get(0) := dlq.io.heads(0).bits
  io.fp_busy_req_uops.get(0) := dlq.io.heads(0).bits

  io.dlq_head.get <> dlq.io.heads(0)
  // Now, update busy info
  when(io.dlq_head.get.bits.lrs1_rtype === RT_FLT) {
    io.dlq_head.get.bits.prs1_busy := io.fp_busy_resps.get(0).prs1_busy
  }.elsewhen(io.dlq_head.get.bits.lrs1_rtype === RT_FIX) {
    io.dlq_head.get.bits.prs1_busy := io.busy_resps.get(0).prs1_busy
  }.otherwise{
    io.dlq_head.get.bits.prs1_busy := false.B
  }

  when(io.dlq_head.get.bits.lrs2_rtype === RT_FLT) {
    io.dlq_head.get.bits.prs2_busy := io.fp_busy_resps.get(0).prs2_busy
  }.elsewhen(io.dlq_head.get.bits.lrs2_rtype === RT_FIX) {
    io.dlq_head.get.bits.prs2_busy := io.busy_resps.get(0).prs2_busy
  }.otherwise{
    io.dlq_head.get.bits.prs2_busy := false.B
  }

  io.dlq_head.get.bits.prs3_busy := io.dlq_head.get.bits.frs3_en && io.fp_busy_resps.get(0).prs3_busy
}

/**
 * LSC Dispatcher - contains both A and B queues and accesses the busy table at their end.
 */
class SliceDispatcher(implicit p: Parameters) extends Dispatcher {
  // Todo: These can probably be removed now. But we need the check somewhere else

  //issue requirements
  require(issueParams(0).iqType == IQT_INT.litValue()) // INT
  require(issueParams(1).iqType == IQT_MEM.litValue()) // MEM

  require(issueParams(0).dispatchWidth == 2)
  require(issueParams(1).dispatchWidth == 2)

  if (usingFPU) {
    require(issueParams(2).iqType == IQT_FP.litValue()) // FP
    require(issueParams(2).dispatchWidth == 1)
  }

  // slice queues
  val a_queue = Module(new SramDispatchQueue( DispatchQueueParams(
    numEntries = boomParams.loadSliceCore.get.numAqEntries,
    qName = "a_queue",
    deqWidth = boomParams.loadSliceCore.get.aDispatches,
    enqWidth = coreWidth))
  )
  val b_queue = Module(new SramDispatchQueue( DispatchQueueParams(
    numEntries = boomParams.loadSliceCore.get.numBqEntries,
    qName = "b_queue",
    deqWidth = boomParams.loadSliceCore.get.bDispatches,
    enqWidth = coreWidth))
  )
  a_queue.io.flush := io.flush.get
  b_queue.io.flush := io.flush.get
  a_queue.io.brinfo := io.brinfo.get
  b_queue.io.brinfo := io.brinfo.get

  a_queue.io.tsc_reg := io.tsc_reg
  b_queue.io.tsc_reg := io.tsc_reg

  val a_heads = WireInit(VecInit(a_queue.io.heads.map(_.bits)))
  val b_heads = WireInit(VecInit(b_queue.io.heads.map(_.bits)))

  //TODO: make this more fine-grained
  val a_ready = a_queue.io.enq_uops.map(_.ready).reduce(_ && _)
  val b_ready = b_queue.io.enq_uops.map(_.ready).reduce(_ && _)


  val queues_ready = a_ready && b_ready
  for (w <- 0 until coreWidth) {
    // TODO: check if it is possible to use only some of the ren_uops
    // only accept uops from rename if both queues are ready
    io.ren_uops(w).ready := queues_ready
    val uop = io.ren_uops(w).bits
    // check if b queue can actually process insn
    // TODO: Analyse: Is it necessary to add a guard protecting agains branches on B-Q? (In case of aliasing in IST)
    val can_use_b_alu = uop.fu_code_is(FUConstants.FU_ALU | FUConstants.FU_MUL | FUConstants.FU_DIV | (FUConstants.FU_BRU)) && !uop.is_br_or_jmp
    val use_b_queue = (uop.uopc === uopLD) || uop.uopc === uopSTA || (uop.is_lsc_b && can_use_b_alu)
    val use_a_queue = (uop.uopc =/= uopLD) && (!uop.is_lsc_b || !can_use_b_alu)

    // enqueue logic
    a_queue.io.enq_uops(w).valid := io.ren_uops(w).fire() && use_a_queue
    b_queue.io.enq_uops(w).valid := io.ren_uops(w).fire() && use_b_queue

    val uop_a = WireInit(uop)
    val uop_b = WireInit(uop)

    assert(!io.ren_uops(w).fire() || (a_queue.io.enq_uops(w).fire() || b_queue.io.enq_uops(w).fire()), "op from rename was swallowed")

    when(uop.uopc === uopSTA) {
      // In case of splitting stores. We need to put data generation in A (uopSTD) and
      //  address generation (uopSTA) in B. We X out the opposite lrs by assigning RT_X to the rtype
      uop_a.uopc := uopSTD
      uop_a.lrs1_rtype := RT_X

      uop_b.uopc := uopSTA
      uop_b.lrs2_rtype := RT_X
      // fsw and fsd fix - they need to go to a -> fp and b -> mem
      when(uop.iq_type === IQT_MFP) {
        uop_b.iq_type := IQT_MEM
        uop_b.lrs2_rtype := RT_X
        uop_a.iq_type := IQT_FP
        uop_a.uopc := uopSTA
        uop_a.lrs1_rtype := RT_X
      }
    }
    a_queue.io.enq_uops(w).bits := uop_a
    b_queue.io.enq_uops(w).bits := uop_b

    assert(!(io.ren_uops(w).fire() && use_b_queue && uop_b.is_br_or_jmp), "[Dispatcher] We are puttig a branch/jump on B-Q")

    // Perf counters
    io.lsc_perf.get.aq(w) := io.ren_uops(w).fire() && use_a_queue
    io.lsc_perf.get.bq(w) := io.ren_uops(w).fire() && use_b_queue && uop.uopc =/= uopSTA
  }

  // annotate heads with busy information
  for ((uop, idx) <- (a_heads ++ b_heads).zipWithIndex) {
    io.busy_req_uops.get(idx) := uop
    val busy_resp = io.busy_resps.get(idx)

    uop.prs1_busy := uop.lrs1_rtype === RT_FIX && busy_resp.prs1_busy
    uop.prs2_busy := uop.lrs2_rtype === RT_FIX && busy_resp.prs2_busy
    uop.prs3_busy := false.B

    //    assert(!(a_valid && busy_resp.prs1_busy && uop.lrs1_rtype === RT_FIX & uop.lrs1 === 0.U), "[rename] x0 is busy??")
    //    assert(!(a_valid && busy_resp.prs2_busy && uop.lrs2_rtype === RT_FIX & uop.lrs2 === 0.U), "[rename] x0 is busy??")
    if (usingFPU) {
      io.fp_busy_req_uops.get(idx) := uop
      val flt_busy_resp = io.fp_busy_resps.get(idx)
      // fp busy info
      when(uop.lrs1_rtype === RT_FLT) {
        uop.prs1_busy := flt_busy_resp.prs1_busy
      }
      when(uop.lrs2_rtype === RT_FLT) {
        uop.prs2_busy := flt_busy_resp.prs2_busy
      }
      uop.prs3_busy := uop.frs3_en && flt_busy_resp.prs3_busy
    }
  }

  // dispatch nothing by default
  for {dis_c <- io.dis_uops
       dis <- dis_c} {
    dis.valid := false.B
    dis.bits := DontCare
  }

  if(boomParams.unifiedIssueQueue){
//    io.dis_uops(LSC_DIS_MEM_PORT_IDX) := DontCare
//    io.dis_uops(3) := DontCare // TODO: clean up
//    if (usingFPU) {
//      io.dis_uops(LSC_DIS_FP_PORT_IDX) := DontCare
//    }
    var dis_idx = 0
    for(i <- 0 until boomParams.loadSliceCore.get.aDispatches){
      val dis = io.dis_uops(LSC_DIS_COMB_PORT_IDX)(dis_idx)
      dis.valid := a_queue.io.heads(i).valid
      a_queue.io.heads(i).ready := dis.ready
      dis.bits := a_heads(i)
      dis_idx += 1
    }
    for(i <- 0 until boomParams.loadSliceCore.get.bDispatches){
      val dis = io.dis_uops(LSC_DIS_COMB_PORT_IDX)(dis_idx)
      dis.valid := b_queue.io.heads(i).valid
      b_queue.io.heads(i).ready := dis.ready
      dis.bits := b_heads(i)
      dis_idx += 1
    }
    require(dis_idx == boomParams.loadSliceCore.get.dispatches)

  } else {
    require(boomParams.loadSliceCore.get.aDispatches == 1)
    require(boomParams.loadSliceCore.get.bDispatches == 1)

    // for now I'm just setting both dispatch ports to the same port - should work since they are never written to at the same time...
    val a_int_dispatch = io.dis_uops(LSC_DIS_INT_PORT_IDX)(LSC_DIS_A_PORT_IDX)
    val a_mem_dispatch = io.dis_uops(LSC_DIS_MEM_PORT_IDX)(LSC_DIS_A_PORT_IDX)
    val a_fp_dispatch = if (usingFPU) Some(io.dis_uops(LSC_DIS_FP_PORT_IDX)(LSC_DIS_A_PORT_IDX)) else None
    val b_int_dispatch = io.dis_uops(LSC_DIS_INT_PORT_IDX)(LSC_DIS_B_PORT_IDX)
    val b_mem_dispatch = io.dis_uops(LSC_DIS_MEM_PORT_IDX)(LSC_DIS_B_PORT_IDX)


    val a_issue_blocked = !a_mem_dispatch.ready || !a_int_dispatch.ready || a_fp_dispatch.map(!_.ready).getOrElse(false.B) // something from a is in a issue slot
    val b_issue_blocked = !b_mem_dispatch.ready || !b_int_dispatch.ready

    val a_head = a_heads(0)
    val b_head = b_heads(0)
    val a_valid = a_queue.io.heads(0).valid
    val b_valid = b_queue.io.heads(0).valid
    val a_deq = WireInit(false.B)
    a_queue.io.heads(0).ready := a_deq
    val b_deq = WireInit(false.B)
    b_queue.io.heads(0).ready := b_deq
    val a_head_mem = (a_head.iq_type & IQT_MEM) =/= 0.U
    val a_head_fp = (a_head.iq_type & IQT_FP) =/= 0.U
    val a_head_int = (a_head.iq_type & IQT_INT) =/= 0.U
    val b_head_mem = b_head.iq_type === IQT_MEM

    // this is handling the ready valid interface stricter than necessary to prevent errors
    // dispatch valid implies dispatch ready
    assert(!a_int_dispatch.valid || a_int_dispatch.ready)
    assert(!b_int_dispatch.valid || b_int_dispatch.ready)
    assert(!a_mem_dispatch.valid || a_mem_dispatch.ready)
    assert(!b_mem_dispatch.valid || b_mem_dispatch.ready)
    if (usingFPU) {
      assert(!a_fp_dispatch.get.valid || a_fp_dispatch.get.ready)
    }

    // dispatch implies dequeue
    assert(!a_int_dispatch.valid || a_deq)
    assert(!b_int_dispatch.valid || b_deq)
    assert(!a_mem_dispatch.valid || a_deq)
    assert(!b_mem_dispatch.valid || b_deq)
    if (usingFPU) {
      assert(!a_fp_dispatch.get.valid || a_deq)
    }

    // dequeue implies dispatch
    assert(!a_deq || (a_int_dispatch.valid || a_mem_dispatch.valid || a_fp_dispatch.map(_.valid).getOrElse(false.B)))
    assert(!b_deq || (b_int_dispatch.valid || b_mem_dispatch.valid))

    a_mem_dispatch.valid := false.B
    a_int_dispatch.valid := false.B
    b_mem_dispatch.valid := false.B
    b_int_dispatch.valid := false.B
    if (usingFPU) {
      a_fp_dispatch.get.valid := false.B
    }

    a_mem_dispatch.bits := a_head
    a_int_dispatch.bits := a_head
    b_mem_dispatch.bits := b_head
    b_int_dispatch.bits := b_head

    if (usingFPU) {
      a_fp_dispatch.get.bits := a_head
    }

    // put uops into issue queues
    when(a_valid && !a_issue_blocked) {
      a_deq := true.B
      when(a_head_mem) {
        a_mem_dispatch.valid := true.B
      }
      when(a_head_fp) {
        if (usingFPU) {
          a_fp_dispatch.get.valid := true.B
        }
      }
      when(a_head_int) {
        a_int_dispatch.valid := true.B
      }
    }
    when(b_valid && !b_issue_blocked) {
      b_deq := true.B
      when(b_head_mem) {
        b_mem_dispatch.valid := true.B
      }.otherwise {
        b_int_dispatch.valid := true.B
      }
    }
  }

  if(O3PIPEVIEW_PRINTF){ // dispatch is here because it does not happen driectly after rename anymore
    for(i <- 0 until boomParams.loadSliceCore.get.aDispatches){
      when (a_queue.io.heads(i).fire()) {
        printf("%d; O3PipeView:dispatch: %d\n", a_queue.io.heads(i).bits.debug_events.fetch_seq, io.tsc_reg)
      }
    }
    for(i <- 0 until boomParams.loadSliceCore.get.bDispatches){
      when (b_queue.io.heads(i).fire()) {
        printf("%d; O3PipeView:dispatch: %d\n", b_queue.io.heads(i).bits.debug_events.fetch_seq, io.tsc_reg)
      }
    }
  }
}

/**
 *  Tries to dispatch as many uops as it can to issue queues,
 *  which may accept fewer than coreWidth per cycle.
 *  When dispatchWidth == coreWidth, its behavior differs
 *  from the BasicDispatcher in that it will only stall dispatch when
 *  an issue queue required by a uop is full.
 */
class CompactingDispatcher(implicit p: Parameters) extends Dispatcher
{
  issueParams.map(ip => require(ip.dispatchWidth >= ip.issueWidth))

  val ren_readys = Wire(Vec(issueParams.size, Vec(coreWidth, Bool())))

  for (((ip, dis), rdy) <- issueParams zip io.dis_uops zip ren_readys) {
    val ren = Wire(Vec(coreWidth, Decoupled(new MicroOp)))
    ren <> io.ren_uops

    val uses_iq = ren map (u => (u.bits.iq_type & ip.iqType.U).orR)

    // Only request an issue slot if the uop needs to enter that queue.
    (ren zip io.ren_uops zip uses_iq) foreach {case ((u,v),q) =>
      u.valid := v.valid && q}

    val compactor = Module(new Compactor(coreWidth, ip.dispatchWidth, new MicroOp))
    compactor.io.in  <> ren
    dis <> compactor.io.out

    // The queue is considered ready if the uop doesn't use it.
    rdy := ren zip uses_iq map {case (u,q) => u.ready || !q}
  }

  (ren_readys.reduce((r,i) =>
      VecInit(r zip i map {case (r,i) =>
        r && i})) zip io.ren_uops) foreach {case (r,u) =>
          u.ready := r}
}

