//******************************************************************************
// Copyright (c) 2015 - 2018, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE and LICENSE.SiFive for license details.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// RISCV Processor Issue Logic
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

package boom.exu

import chisel3._
import chisel3.util._

import freechips.rocketchip.config.Parameters
import freechips.rocketchip.util.{Str}

import boom.common._
import boom.exu.FUConstants._
import boom.util.{BoolToChar}

/**
 * Class used for configurations
 *
 * @param issueWidth amount of things that can be issued
 * @param numEntries size of issue queue
 * @param iqType type of issue queue
 */
case class IssueParams(
  dispatchWidth: Int = 1,
  issueWidth: Int = 1,
  numEntries: Int = 8,
  iqType: BigInt
)

/**
 * Constants for knowing about the status of a MicroOp
 */
trait IssueUnitConstants
{
  // invalid  : slot holds no valid uop.
  // s_valid_1: slot holds a valid uop.
  // s_valid_2: slot holds a store-like uop that may be broken into two micro-ops.
  val s_invalid :: s_valid_1 :: s_valid_2 :: Nil = Enum(3)
}

/**
 * What physical register is broadcasting its wakeup?
 * Is the physical register poisoned (aka, was it woken up by a speculative issue)?
 *
 * @param pregSz size of physical destination register
 */
class IqWakeup(val pregSz: Int)(implicit p: Parameters) extends BoomBundle
{
  val reg_type = if(boomParams.unifiedIssueQueue) Some(UInt(2.W)) else None //TODO: maybe make this only one bit
  val pdst = UInt(width=pregSz.W)
  val poisoned = Bool()
}

/**
 * IO bundle to interact with the issue unit
 *
 * @param issueWidth amount of operations that can be issued at once
 * @param numWakeupPorts number of wakeup ports for issue unit
 */
class IssueUnitIO(
  val issueWidth: Int,
  val numWakeupPorts: Int,
  val dispatchWidth: Int)
  (implicit p: Parameters) extends BoomBundle
{
  val dis_uops         = Vec(dispatchWidth, Flipped(Decoupled(new MicroOp)))

  val iss_valids       = Output(Vec(issueWidth, Bool()))
  val iss_uops         = Output(Vec(issueWidth, new MicroOp()))
  val wakeup_ports     = Flipped(Vec(numWakeupPorts, Valid(new IqWakeup(maxPregSz))))

  val spec_ld_wakeup  = Flipped(Valid(UInt(width=maxPregSz.W)))

  // tell the issue unit what each execution pipeline has in terms of functional units
  val fu_types         = Input(Vec(issueWidth, Bits(width=FUC_SZ.W)))
  val iq_types         = if(boomParams.unifiedIssueQueue) Some(Input(Vec(issueWidth, Bits(width=IQT_SZ.W)))) else None

  val brinfo           = Input(new BrResolutionInfo())
  val flush_pipeline   = Input(Bool())
  val ld_miss          = Input(Bool())

  val event_empty      = Output(Bool()) // used by HPM events; is the issue unit empty?

  val tsc_reg          = Input(UInt(width=xLen.W))

  // DnB ports to Dispatch
  val dlq_head = if(boomParams.dnbMode) Some(Vec(boomParams.dnbParams.get.dlqDispatches, Flipped(DecoupledIO(new MicroOp)))) else None
  val crq_head = if(boomParams.dnbMode) Some(Vec(boomParams.dnbParams.get.crqDispatches, Flipped(DecoupledIO(new MicroOp)))) else None
  val rob_head_idx = if(boomParams.dnbMode) Some(Input(UInt(robAddrSz.W))) else None

  // CASINO ports to Dispatch
  val inq_heads = if(boomParams.casMode) Some(Vec(boomParams.casParams.get.inqDispatches, Flipped(DecoupledIO(new MicroOp)))) else None
  val sq_heads = if(boomParams.casMode) Some(Vec(boomParams.casParams.get.windowSize, Flipped(DecoupledIO(new MicroOp)))) else None

}

/**
 * Abstract top level issue unit
 *
 * @param numIssueSlots depth of issue queue
 * @param issueWidth amoutn of operations that can be issued at once
 * @param numWakeupPorts number of wakeup ports for issue unit
 * @param iqType type of issue queue (mem, int, fp)
 */
abstract class IssueUnit(
  val numIssueSlots: Int,
  val issueWidth: Int,
  val numWakeupPorts: Int,
  val iqType: BigInt,
  val dispatchWidth: Int)
  (implicit p: Parameters)
  extends BoomModule
  with IssueUnitConstants
{
  val io = IO(new IssueUnitIO(issueWidth, numWakeupPorts, dispatchWidth))

  //-------------------------------------------------------------
  // Set up the dispatch uops
  // special case "storing" 2 uops within one issue slot.

  val dis_uops = Array.fill(dispatchWidth) {Wire(new MicroOp())}
  for (w <- 0 until dispatchWidth) {
    dis_uops(w) := io.dis_uops(w).bits
    dis_uops(w).iw_p1_poisoned := false.B
    dis_uops(w).iw_p2_poisoned := false.B
    dis_uops(w).iw_state := s_valid_1

    // all of the store splitting logic is handled in dispatch for the LSC
    require(!(iqType == IQT_COMB.litValue()) || boomParams.loadSliceMode || boomParams.dnbMode, "combined issue queue only in lsc mode")
    if(!boomParams.loadSliceMode && !boomParams.dnbMode) {
      if (iqType == IQT_MEM.litValue || iqType == IQT_INT.litValue) {
        // For StoreAddrGen for Int, or AMOAddrGen, we go to addr gen state
        when((io.dis_uops(w).bits.uopc === uopSTA && io.dis_uops(w).bits.lrs2_rtype === RT_FIX) ||
          io.dis_uops(w).bits.uopc === uopAMO_AG) {
          dis_uops(w).iw_state := s_valid_2
          // For store addr gen for FP, rs2 is the FP register, and we don't wait for that here
        }.elsewhen(io.dis_uops(w).bits.uopc === uopSTA && io.dis_uops(w).bits.lrs2_rtype =/= RT_FIX) {
          dis_uops(w).lrs2_rtype := RT_X
          dis_uops(w).prs2_busy := false.B
        }
        dis_uops(w).prs3_busy := false.B
      } else if (iqType == IQT_FP.litValue) {
        // FP "StoreAddrGen" is really storeDataGen, and rs1 is the integer address register
        when(io.dis_uops(w).bits.uopc === uopSTA) {
          dis_uops(w).lrs1_rtype := RT_X
          dis_uops(w).prs1_busy := false.B
        }
      }
    }
  }

  //-------------------------------------------------------------
  // Issue Table

  val slots = for (i <- 0 until numIssueSlots) yield { val slot = Module(new IssueSlot(numWakeupPorts)); slot }
  val issue_slots = if(!boomParams.casMode) {
    VecInit(slots.map(_.io))
  } else {
    null
  }

  if (!boomParams.casMode) {
    io.event_empty := !(issue_slots.map(s => s.valid).reduce(_ | _))
    if (DEBUG_PRINTF_IQ) {
      printf(this.getType + " issue slots:\n")
      for (i <- 0 until numIssueSlots) {
        printf("    Slot[%d]: " +
          "V:%c Req:%c Wen:%c P:(%c,%c,%c) PRegs:Dst:(Typ:%c #:%d) Srcs:(%d,%d,%d) " +
          "[PC:0x%x Inst:DASM(%x) UOPCode:%d] RobIdx:%d BMsk:0x%x Imm:0x%x\n",
          i.U(log2Ceil(numIssueSlots + 1).W),
          BoolToChar(issue_slots(i).valid, 'V'),
          BoolToChar(issue_slots(i).request, 'R'),
          BoolToChar(issue_slots(i).in_uop.valid, 'W'),
          BoolToChar(issue_slots(i).debug.p1, '!'),
          BoolToChar(issue_slots(i).debug.p2, '!'),
          BoolToChar(issue_slots(i).debug.p3, '!'),
          Mux(issue_slots(i).uop.dst_rtype === RT_FIX, Str("X"),
            Mux(issue_slots(i).uop.dst_rtype === RT_X, Str("-"),
              Mux(issue_slots(i).uop.dst_rtype === RT_FLT, Str("f"),
                Mux(issue_slots(i).uop.dst_rtype === RT_PAS, Str("C"), Str("?"))))),
          issue_slots(i).uop.pdst,
          issue_slots(i).uop.prs1,
          issue_slots(i).uop.prs2,
          issue_slots(i).uop.prs3,
          issue_slots(i).uop.debug_pc(31, 0),
          issue_slots(i).uop.debug_inst,
          issue_slots(i).uop.uopc,
          issue_slots(i).uop.rob_idx,
          issue_slots(i).uop.br_mask,
          issue_slots(i).uop.imm_packed)
      }
    }

    //-------------------------------------------------------------

    assert(PopCount(issue_slots.map(s => s.grant)) <= issueWidth.U, "[issue] window giving out too many grants.")

  }

  //-------------------------------------------------------------

  if (O3PIPEVIEW_PRINTF) {
    for (i <- 0 until issueWidth) {
      // only print stores once!
      when (io.iss_valids(i) && io.iss_uops(i).uopc =/= uopSTD) {
         printf("%d; O3PipeView:issue: %d\n",
           io.iss_uops(i).debug_events.fetch_seq,
           io.tsc_reg)
      }
    }
  }


  def getType: String =
    if (iqType == IQT_INT.litValue) "int"
    else if (iqType == IQT_MEM.litValue) "mem"
    else if (iqType == IQT_FP.litValue) " fp"
    else if (iqType == IQT_COMB.litValue) " uni"
    else "unknown"
}
