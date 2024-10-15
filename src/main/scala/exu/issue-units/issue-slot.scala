//******************************************************************************
// Copyright (c) 2015 - 2018, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE and LICENSE.SiFive for license details.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// RISCV Processor Issue Slot Logic
//--------------------------------------------------------------------------
//------------------------------------------------------------------------------
//
// Note: stores (and AMOs) are "broken down" into 2 uops, but stored within a single issue-slot.
// TODO XXX make a separate issueSlot for MemoryIssueSlots, and only they break apart stores.
// TODO Disable ldspec for FP queue.

package boom.exu

import chisel3._
import chisel3.util._

import freechips.rocketchip.config.Parameters

import boom.common._
import boom.util._
import FUConstants._

/**
 * IO bundle to interact with Issue slot
 *
 * @param numWakeupPorts number of wakeup ports for the slot
 */
class IssueSlotIO(val numWakeupPorts: Int)(implicit p: Parameters) extends BoomBundle
{
  val valid         = Output(Bool())
  val will_be_valid = Output(Bool()) // TODO code review, do we need this signal so explicitely?
  val request       = Output(Bool())
  val request_hp    = Output(Bool())
  val grant         = Input(Bool())

  val brupdate        = Input(new BrUpdateInfo())
  val kill          = Input(Bool()) // pipeline flush
  val clear         = Input(Bool()) // entry being moved elsewhere (not mutually exclusive with grant)
  val ldspec_miss   = Input(Bool()) // Previous cycle's speculative load wakeup was mispredicted.

  val wakeup_ports  = Flipped(Vec(numWakeupPorts, Valid(new IqWakeup(maxPregSz))))
  val pred_wakeup_port = Flipped(Valid(UInt(log2Ceil(ftqSz).W)))
  val spec_ld_wakeup = Flipped(Vec(memWidth, Valid(UInt(width=maxPregSz.W))))
  //Taint Tracking
  val taint_wakeup_port = Flipped(Vec(numTaintWakeupPorts, Valid(UInt(ldqAddrSz.W))))
  val yrot_resp = if (enableRegisterTaintTracking) Input(Valid(new RegYrotResp())) else null

  val blocked_taint = Output(Bool())

  //Taint debug
  val ldq_head = Input(UInt(ldqAddrSz.W))
  val ldq_tail = Input(UInt(ldqAddrSz.W))

  val in_uop        = Flipped(Valid(new MicroOp())) // if valid, this WILL overwrite an entry!
  val out_uop   = Output(new MicroOp()) // the updated slot uop; will be shifted upwards in a collasping queue.
  val uop           = Output(new MicroOp()) // the current Slot's uop. Sent down the pipeline when issued.

  val debug = {
    val result = new Bundle {
      val p1 = Bool()
      val p2 = Bool()
      val p3 = Bool()
      val yrot_r = Bool()
      val ppred = Bool()
      val state = UInt(width=2.W)
    }
    Output(result)
  }
}

/**
 * Single issue slot. Holds a uop within the issue queue
 *
 * @param numWakeupPorts number of wakeup ports
 */
class IssueSlot(val numWakeupPorts: Int)(implicit p: Parameters)
  extends BoomModule
  with IssueUnitConstants
{
  val io = IO(new IssueSlotIO(numWakeupPorts))

  // slot invalid?
  // slot is valid, holding 1 uop
  // slot is valid, holds 2 uops (like a store)
  def is_invalid = state === s_invalid
  def is_valid = state =/= s_invalid

  val next_state      = Wire(UInt()) // the next state of this slot (which might then get moved to a new slot)
  val next_uopc       = Wire(UInt()) // the next uopc of this slot (which might then get moved to a new slot)
  val next_state_uopc = Wire(UInt())
  val next_lrs1_rtype = Wire(UInt()) // the next reg type of this slot (which might then get moved to a new slot)
  val next_lrs2_rtype = Wire(UInt()) // the next reg type of this slot (which might then get moved to a new slot)
  val partial_reset   = Wire(Bool()) // Should the taint calc be reset due to a partial issue

  val state = RegInit(s_invalid)
  val previous_state = RegInit(s_invalid)
  val state_uopc = RegInit(0.U(UOPC_SZ.W))
  val p1    = RegInit(false.B)
  val p2    = RegInit(false.B)
  val p3    = RegInit(false.B)
  val ppred = RegInit(false.B)
  val yrot_r = RegInit(false.B)

  // Poison if woken up by speculative load.
  // Poison lasts 1 cycle (as ldMiss will come on the next cycle).
  // SO if poisoned is true, set it to false!
  val p1_poisoned = RegInit(false.B)
  val p2_poisoned = RegInit(false.B)
  p1_poisoned := false.B
  p2_poisoned := false.B
  val next_p1_poisoned = Mux(io.in_uop.valid, io.in_uop.bits.iw_p1_poisoned, p1_poisoned)
  val next_p2_poisoned = Mux(io.in_uop.valid, io.in_uop.bits.iw_p2_poisoned, p2_poisoned)

  val slot_uop = RegInit(NullMicroOp)
  val next_uop = Mux(io.in_uop.valid, io.in_uop.bits, slot_uop)

  //-----------------------------------------------------------------------------
  // next slot state computation
  // compute the next state for THIS entry slot (in a collasping queue, the
  // current uop may get moved elsewhere, and a new uop can enter

  when (io.kill) {
    state := s_invalid
    previous_state := s_invalid
    state_uopc := 0.U
  } .elsewhen (io.in_uop.valid) {
    state := io.in_uop.bits.iw_state
    previous_state := io.in_uop.bits.old_iw_state
    state_uopc := io.in_uop.bits.state_uopc
  } .elsewhen (io.clear) {
    state := s_invalid
    previous_state := s_invalid
    state_uopc := 0.U
  } .otherwise {
    state := next_state
    previous_state := state
    slot_uop.uopc := next_uopc
    state_uopc := next_state_uopc
    slot_uop.lrs1_rtype := next_lrs1_rtype
    slot_uop.lrs2_rtype := next_lrs2_rtype
  }

  //-----------------------------------------------------------------------------
  // "update" state
  // compute the next state for the micro-op in this slot. This micro-op may
  // be moved elsewhere, so the "next_state" travels with it.

  // defaults
  next_state := state
  next_uopc := slot_uop.uopc
  next_state_uopc := slot_uop.uopc
  next_lrs1_rtype := slot_uop.lrs1_rtype
  next_lrs2_rtype := slot_uop.lrs2_rtype
  partial_reset := false.B

  when (io.kill) {
    next_state := s_invalid
  } .elsewhen ((io.grant && (state === s_valid_1)) ||
    (io.grant && (state === s_valid_2) && p1 && p2 && ppred)) {
    // try to issue this uop.
    if (enableRegisterTaintTracking) {
    when (!(io.ldspec_miss && (p1_poisoned || p2_poisoned))) {
      next_state := Mux(slot_uop.taint_set || !slot_uop.transmitter, s_invalid, s_taint_blocked)
      when(state === s_valid_2) {
          slot_uop.state_uopc := 0.U
          next_state_uopc := 0.U
      }
      }
    } else {
    when (!(io.ldspec_miss && (p1_poisoned || p2_poisoned))) {
      next_state := s_invalid
      }
    } 
  } .elsewhen (io.grant && (state === s_valid_2)) {
    val is_valid_s2_grant = WireInit(false.B)
    is_valid_s2_grant := !(io.ldspec_miss && (p1_poisoned || p2_poisoned)) && yrot_r

    when (is_valid_s2_grant) {
      if (enableRegisterTaintTracking) {
        next_state := Mux(slot_uop.taint_set, s_valid_1, s_taint_blocked)
      } else {
        next_state := s_valid_1
      }
      when(slot_uop.taint_set) {
        when (p1) {
          next_uopc := uopSTD
          next_lrs1_rtype := RT_X
        } .otherwise {
          next_lrs2_rtype := RT_X
        }
      }.otherwise {
        assert(slot_uop.uopc === uopSTA || slot_uop.uopc === uopAMO_AG)
        assert(!(p1 && p2 && ppred))
        when(p1) {
          next_state_uopc := uopSTD
        }.otherwise {
          next_state_uopc := slot_uop.uopc
        }
      }
    }
  } .elsewhen (state === s_taint_blocked) {

    assert(!(previous_state === s_invalid))
    assert(!(previous_state === s_taint_blocked))
    assert(previous_state === s_valid_1 || previous_state === s_valid_2)
    assert(enableRegisterTaintTracking.B)
    
    //Partial dispatch, i.e. we sent data or address to stq
    when(yrot_r && previous_state === s_valid_2 &&
        (state_uopc === uopSTD || state_uopc === uopSTA || state_uopc === uopAMO_AG)) {
      next_state := s_valid_1
      next_uopc := state_uopc
      partial_reset := true.B //taint calc succeeded for one operand, but not yet for other
      //This happens when an s_valid_2 has both operands ready and can terminate
      //This should never trip cause state_uopc has to be something othern than 0.U
      //TODO: Can remove?
      when(state_uopc === 0.U) {
        next_state := s_invalid
      }
      .elsewhen(state_uopc === uopSTD) {
        next_uopc := uopSTD
        next_lrs1_rtype := RT_X
      }.otherwise {
        next_lrs2_rtype := RT_X
      }
    //Full dispatch, we sent full uop and yrot was valid
    }.elsewhen((yrot_r && previous_state === s_valid_2) ||
              (yrot_r && previous_state === s_valid_1)) {
      next_state := s_invalid
    //Failed dispatch
    }.elsewhen(!yrot_r) {
      next_state := previous_state
    }.otherwise{
      //We did something wrong, we should always be leaving this state
      assert(false.B)
    }
  }

  when (io.in_uop.valid) {
    slot_uop := io.in_uop.bits
    assert (is_invalid || io.clear || io.kill, "trying to overwrite a valid issue slot.")
  }.otherwise{
    if (enableRegisterTaintTracking) {
    slot_uop.taint_set  := Mux(io.grant, true.B, slot_uop.taint_set)
    slot_uop.yrot       := Mux(io.yrot_resp.valid, io.yrot_resp.bits.yrot, slot_uop.yrot)
    yrot_r              := Mux(io.yrot_resp.valid, io.yrot_resp.bits.yrot_r, yrot_r)
    } else {
    // Taint is always set (not used for unsecure and NDA) if we are not doing regtaint
    slot_uop.taint_set  := true.B
    slot_uop.yrot       := slot_uop.yrot
    yrot_r              := yrot_r
    }
  }
  // Wakeup Compare Logic

  // these signals are the "next_p*" for the current slot's micro-op.
  // they are important for shifting the current slot_uop up to an other entry.
  val next_p1 = WireInit(p1)
  val next_p2 = WireInit(p2)
  val next_p3 = WireInit(p3)
  val next_ppred = WireInit(ppred)

  when (io.in_uop.valid) {
    p1 := !(io.in_uop.bits.prs1_busy)
    p2 := !(io.in_uop.bits.prs2_busy)
    p3 := !(io.in_uop.bits.prs3_busy)
    ppred := !(io.in_uop.bits.ppred_busy)
    // STT
    yrot_r := io.in_uop.bits.yrot_r
    // End STT
  }

  when (io.ldspec_miss && next_p1_poisoned) {
    assert(next_uop.prs1 =/= 0.U, "Poison bit can't be set for prs1=x0!")
    p1 := false.B
  }
  when (io.ldspec_miss && next_p2_poisoned) {
    assert(next_uop.prs2 =/= 0.U, "Poison bit can't be set for prs2=x0!")
    p2 := false.B
  }

  for (i <- 0 until numWakeupPorts) {
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs1)) {
      p1 := true.B
    }
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs2)) {
      p2 := true.B
    }
    when (io.wakeup_ports(i).valid &&
         (io.wakeup_ports(i).bits.pdst === next_uop.prs3)) {
      p3 := true.B
    }
  }

  // STT
  for (i <- 0 until numTaintWakeupPorts) {
    when (next_uop.taint_set &&
         io.taint_wakeup_port(i).valid &&
        (io.taint_wakeup_port(i).bits === next_uop.yrot)) {
      yrot_r := true.B
    }
  }
  
  def idxBetween(idx: UInt, ldq_head: UInt, ldq_tail: UInt) : Bool = {
        val isBetween = Mux(ldq_head <= ldq_tail,
                           (ldq_head <= idx) && (idx < ldq_tail),
                           (ldq_head <= idx) || (idx < ldq_tail))

        isBetween
    }
  // End STT
  
  when (io.pred_wakeup_port.valid && io.pred_wakeup_port.bits === next_uop.ppred) {
    ppred := true.B
  }

  for (w <- 0 until memWidth) {
    assert (!(io.spec_ld_wakeup(w).valid && io.spec_ld_wakeup(w).bits === 0.U),
      "Loads to x0 should never speculatively wakeup other instructions")
  }

  // TODO disable if FP IQ.
  for (w <- 0 until memWidth) {
    when (io.spec_ld_wakeup(w).valid &&
      io.spec_ld_wakeup(w).bits === next_uop.prs1 &&
      next_uop.lrs1_rtype === RT_FIX) {
      p1 := true.B
      p1_poisoned := true.B
      assert (!next_p1_poisoned)
    }
    when (io.spec_ld_wakeup(w).valid &&
      io.spec_ld_wakeup(w).bits === next_uop.prs2 &&
      next_uop.lrs2_rtype === RT_FIX) {
      p2 := true.B
      p2_poisoned := true.B
      assert (!next_p2_poisoned)
    }
  }


  // Handle branch misspeculations
  val next_br_mask = GetNewBrMask(io.brupdate, slot_uop)

  // was this micro-op killed by a branch? if yes, we can't let it be valid if
  // we compact it into an other entry
  when (IsKilledByBranch(io.brupdate, slot_uop)) {
    next_state := s_invalid
  }

  when (!io.in_uop.valid) {
    slot_uop.br_mask := next_br_mask
  }


  assert(!(!yrot_r && slot_uop.is_problematic))

  //-------------------------------------------------------------
  // Request Logic - yrot_r is STT
  // yrot_r always high if STT is disabled
  io.request := is_valid && p1 && p2 && p3 && ppred && yrot_r && !io.kill && state =/= s_taint_blocked
  io.blocked_taint := is_valid && p1 && p2 && p3 && ppred && !io.kill && !yrot_r
  val high_priority = slot_uop.is_br || slot_uop.is_jal || slot_uop.is_jalr
  io.request_hp := io.request && high_priority

  when (state === s_valid_1) {
    // yrot_r is STT
    if (inOrderBranchResolution) {
      val ready = p1 && p2 && p3 && ppred && yrot_r && !io.kill
      io.request := Mux(slot_uop.is_br, ready && next_br_mask === 0.U, ready)
    } else {
      io.request := p1 && p2 && p3 && ppred && yrot_r && !io.kill
    }
  } .elsewhen (state === s_valid_2) {
    io.request := (p1 || p2) && ppred && yrot_r && !io.kill
  }.otherwise {
    io.request := false.B
  }
  


  //assign outputs
  io.valid := is_valid
  io.uop := slot_uop
  io.uop.iw_p1_poisoned := p1_poisoned
  io.uop.iw_p2_poisoned := p2_poisoned

  // micro-op will vacate due to grant.
  val may_vacate = io.grant && ((state === s_valid_1) || (state === s_valid_2) && p1 && p2 && ppred && yrot_r)
  val squash_grant = io.ldspec_miss && (p1_poisoned || p2_poisoned) 
  val taint_squash_vacate = if (enableRegisterTaintTracking) !slot_uop.taint_set && slot_uop.transmitter else false.B
  io.will_be_valid := is_valid && !(may_vacate && !squash_grant && !taint_squash_vacate) && !(next_state === s_invalid)

  io.out_uop            := slot_uop
  io.out_uop.iw_state   := next_state
  io.out_uop.old_iw_state := state
  io.out_uop.state_uopc := next_state_uopc
  io.out_uop.uopc       := next_uopc
  io.out_uop.lrs1_rtype := next_lrs1_rtype
  io.out_uop.lrs2_rtype := next_lrs2_rtype
  io.out_uop.br_mask    := next_br_mask
  io.out_uop.prs1_busy  := !p1
  io.out_uop.prs2_busy  := !p2
  io.out_uop.prs3_busy  := !p3
  if (enableRegisterTaintTracking) {
  io.out_uop.yrot       := Mux(io.yrot_resp.valid, io.yrot_resp.bits.yrot, slot_uop.yrot)
  io.out_uop.yrot_r     := Mux(io.yrot_resp.valid, io.yrot_resp.bits.yrot_r, yrot_r)
  io.out_uop.taint_set  := Mux(io.grant, true.B, Mux(partial_reset, false.B, slot_uop.taint_set))
  } else {
  io.out_uop.yrot := slot_uop.yrot
  io.out_uop.yrot_r := yrot_r
  io.out_uop.taint_set := true.B
  }
  io.out_uop.ppred_busy := !ppred
  io.out_uop.iw_p1_poisoned := p1_poisoned
  io.out_uop.iw_p2_poisoned := p2_poisoned

  when (state === s_valid_2) {
    when (p1 && p2 && ppred) {
      ; // send out the entire instruction as one uop
    } .elsewhen (p1 && ppred) {
      io.uop.uopc := slot_uop.uopc
      io.uop.lrs2_rtype := RT_X
    } .elsewhen (p2 && ppred) {
      io.uop.uopc := uopSTD
      io.uop.lrs1_rtype := RT_X
    }
  }

  // debug outputs
  io.debug.p1 := p1
  io.debug.p2 := p2
  io.debug.p3 := p3
  io.debug.ppred := ppred
  io.debug.state := state
}
