package lsc

import boom.exu.CommitSignals
import chisel3._
import chisel3.util._
import freechips.rocketchip.config.Parameters
import boom.common._

/**
  * Custom commit signals combining ROBs commit signals
  * with a tag that could arrive from somewhere else (like the FTQ)
  * @param
  */

class RdtUpdateSignals(implicit p: Parameters) extends BoomBundle
{
  val valid = Bool()
  val tag  = UInt(IbdaParams.ibda_tag_sz.W)
  val uop = new MicroOp
}

class RdtIO(implicit p: Parameters) extends BoomBundle
{
  val update = Input(Vec(decodeWidth, new RdtUpdateSignals))
  val mark = Output(new IstMark)
}

class RegisterDependencyTable(implicit p: Parameters) extends BoomModule{
  val io = IO(new RdtIO)

  val rdt = Reg(Vec(boomParams.numIntPhysRegisters, UInt(IbdaParams.ibda_tag_sz.W)))
  val commit_dst_valid = WireInit(VecInit(Seq.fill(decodeWidth)(false.B)))

  io.mark := DontCare
  io.mark.mark.map(_.valid := false.B)

  for(i <- 0 until decodeWidth){


    val uop = io.update(i).uop
    val valid = io.update(i).valid
    val tag = io.update(i).tag

    // record pc of last insn that committed to reg
    when(valid && uop.dst_rtype === RT_FIX && uop.ldst =/= 0.U){
      rdt(uop.ldst) := tag
      commit_dst_valid(i) := true.B
    }

    val is_b = uop.is_lsc_b || uop.uopc === uopLD || uop.uopc === uopSTA || uop.uopc === uopSTD
    // add pcs of dependent insns to ist
    when(valid && is_b){
      when(uop.lrs1_rtype === RT_FIX && uop.lrs1 =/= 0.U){
        io.mark.mark(2*i).valid := true.B
        io.mark.mark(2*i).bits := rdt(uop.prs1)
        // bypass rdt for previous insns committed in same cycle
        for (j <- 0 until i){
          val uop_j = io.update(j).uop
          when(commit_dst_valid(j) && uop_j.ldst === uop.prs1){
            io.mark.mark(2*i).bits := io.update(i).tag
          }
        }
      }
      when(uop.lrs2_rtype === RT_FIX && uop.lrs2 =/= 0.U){
        io.mark.mark(2*i+1).valid := true.B
        io.mark.mark(2*i+1).bits := rdt(uop.prs2)
        // bypass rdt for previous insns committed in same cycle
        for (j <- 0 until i){
          val uop_j = io.update(j).uop
          when(commit_dst_valid(j) && uop_j.ldst === uop.prs2){
            io.mark.mark(2*i).bits := io.update(j).tag
          }
        }
      }
    }
  }
}