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

import boom.common._
import boom.util.WrapInc
import chisel3._
import chisel3.internal.naming.chiselName
import chisel3.util.{PopCount, isPow2, log2Ceil}
import freechips.rocketchip.config.Parameters

/**
  * Specific type of issue unit
  *
  * @param params issue queue params
  * @param numWakeupPorts number of wakeup ports for the issue queue
  */
@chiselName
class IssueUnitDnbUnified(
                           params: IssueParams,
                           numWakeupPorts: Int)
                           (implicit p: Parameters)
  extends IssueUnit(params.numEntries, params.issueWidth, numWakeupPorts, params.iqType, params.dispatchWidth)
{
  val dnbParams = boomParams.dnbParams.get
  //TODO: figure out how to allocate some issue port explicitly fro DLQ and CRQ?
  //TODO: allow non-urgent dlq insns if fu is available?
  // we need this so we can enqueue it
  val dlq_uop = Wire(Vec(dnbParams.dlqDispatches, new MicroOp))
  val dlq_request = Wire(Vec(dnbParams.dlqDispatches, Bool()))
  val dlq_urgent = Wire(Vec(dnbParams.dlqDispatches, Bool()))
  val dlq_will_be_valid = Wire(Vec(dnbParams.dlqDispatches, Bool()))
  val dlq_grant = Wire(Vec(dnbParams.dlqDispatches, Bool()))
  val dlq_grant_urgent = Wire(Vec(dnbParams.dlqDispatches, Bool()))
  val dlq_to_slot = Wire(Vec(dnbParams.dlqDispatches, Bool()))


  for(i <- 0 until dnbParams.dlqDispatches) {
    dlq_uop(i) := io.dlq_head.get(i).bits
    dlq_uop(i).iw_p1_poisoned := false.B
    dlq_uop(i).iw_p2_poisoned := false.B
    dlq_uop(i).iw_state := s_valid_1
    val dlq_head_dist = Wire(UInt(robAddrSz.W))
    // rob_head_idx + dlqRobUrgentDist >= dlq_head.rob_idx
    when(io.rob_head_idx.get <= dlq_uop(i).rob_idx){
      dlq_head_dist := dlq_uop(i).rob_idx - io.rob_head_idx.get
    }.otherwise{
      // wrap around case
      val max_rob_head = (numRobRows << log2Ceil(coreWidth)).U
      dlq_head_dist := (dlq_uop(i).rob_idx +& max_rob_head) - io.rob_head_idx.get
    }
    val dlq_near_head = WireInit(dlq_head_dist  < boomParams.dnbParams.get.dlqRobUrgentDist.U)
    dlq_urgent(i) := io.dlq_head.get(i).valid && dlq_near_head
    val dlq_busy = (dlq_uop(i).prs1_busy || dlq_uop(i).prs2_busy || dlq_uop(i).prs3_busy)
    dlq_request(i) := io.dlq_head.get(i).valid && !dlq_busy
    dlq_grant_urgent(i) := false.B
    dlq_grant(i) := false.B
    dlq_will_be_valid(i) := dlq_urgent(i) && !dlq_grant_urgent(i)
    dlq_to_slot(i) := false.B
    io.dlq_head.get(i).ready := dlq_grant_urgent(i) || dlq_to_slot(i) || dlq_grant(i)

    assert(!((dlq_grant(i) || dlq_grant_urgent(i)) && dlq_to_slot(i) && io.dlq_head.get(i).valid), "[dnb-iu] DLQ head is both issued and added to IQ")
    assert(!( io.dlq_head.get(i).valid && dlq_urgent(i) && !(dlq_to_slot(i) || dlq_grant_urgent(i))), "[dnb-iu] DLQ head is urgent but is not added to IQ nor granted")
  }


  //-------------------------------------------------------------
  // Figure out how much to shift entries by

  // need to be able to shift by one mor in order to incorporate dlq
  val maxShift = dispatchWidth+dnbParams.dlqDispatches
  // TODO: figure out if this might increase the critical path
  val vacants = issue_slots.map(s => !(s.valid)) ++ dlq_urgent.map(!_) ++ io.dis_uops.map(_.valid).map(!_.asBool)
  val shamts_oh = Array.fill(numIssueSlots+maxShift) {Wire(UInt(width=maxShift.W))}
  // track how many to shift up this entry by by counting previous vacant spots
  def SaturatingCounterOH(count_oh:UInt, inc: Bool, max: Int): UInt = {
    val next = Wire(UInt(width=max.W))
    next := count_oh
    when (count_oh === 0.U && inc) {
      next := 1.U
    } .elsewhen (!count_oh(max-1) && inc) {
      next := (count_oh << 1.U)
    }
    next
  }
  shamts_oh(0) := 0.U
  for (i <- 1 until numIssueSlots + maxShift) {
    shamts_oh(i) := SaturatingCounterOH(shamts_oh(i-1), vacants(i-1), maxShift)
  }

  //-------------------------------------------------------------

  // which entries' uops will still be next cycle? (not being issued and vacated)
  val will_be_valid = (0 until numIssueSlots).map(i => issue_slots(i).will_be_valid) ++
    dlq_will_be_valid ++
    (0 until dispatchWidth).map(i => io.dis_uops(i).valid &&
      !dis_uops(i).exception &&
      !dis_uops(i).is_fence &&
      !dis_uops(i).is_fencei)

  val debug_shift_src = WireInit(VecInit(Seq.fill(numIssueSlots)(0.U(10.W))))
  dontTouch(debug_shift_src)
  val queue_added = WireInit(VecInit(Seq.fill(maxShift)(false.B)))
  dontTouch(queue_added)
  val uops = issue_slots.map(s=>s.out_uop) ++
    dlq_uop ++
    dis_uops.map(s=>s)
  for (i <- 0 until numIssueSlots) {
    issue_slots(i).in_uop.valid := false.B
    issue_slots(i).in_uop.bits  := uops(i+1)
    for (j <- 1 to maxShift by 1) {
      when (shamts_oh(i+j) === (1 << (j-1)).U) {
        issue_slots(i).in_uop.valid := will_be_valid(i+j)
        issue_slots(i).in_uop.bits  := uops(i+j)
        if(i+j >= numIssueSlots){
          queue_added(i+j-numIssueSlots) := will_be_valid(i+j)
        }
        debug_shift_src(i) := (i+j).U
      }
    }
    issue_slots(i).wakeup_ports := io.wakeup_ports
    issue_slots(i).ldspec_dst   := io.spec_ld_wakeup
    issue_slots(i).ldspec_miss  := io.ld_miss
    issue_slots(i).brinfo       := io.brinfo
    issue_slots(i).kill         := io.flush_pipeline
    issue_slots(i).clear        := shamts_oh(i) =/= 0.U
  }

  //-------------------------------------------------------------
  // Dispatch/Entry Logic
  // did we find a spot to slide the new dispatched uops into?
  val will_be_available = (0 until numIssueSlots).map(i =>
    (!issue_slots(i).will_be_valid || issue_slots(i).clear) && !(issue_slots(i).in_uop.valid))
  //TODO: maybe also change behavior for DLQ
  val num_available = PopCount(will_be_available)
  for (i <- 0 until dnbParams.dlqDispatches) {
    dlq_to_slot(i) := queue_added(i) && dlq_will_be_valid(i)
  }
  for (w <- 0 until dispatchWidth) {
//    assert(!queue_added(w+1) || io.dis_uops(w).ready, f"IQ: dispatch $w had ready logic error")
//    assert(!io.dis_uops(w).fire() || queue_added(w), f"IQ: dispatch $w had ready logic error")
    io.dis_uops(w).ready := RegNext(num_available > (w+1).U)
  }
  //-------------------------------------------------------------
  // Issue Select Logic

  // set default
  for (w <- 0 until issueWidth) {
    io.iss_valids(w) := false.B
    io.iss_uops(w)   := NullMicroOp
    // unsure if this is overkill
    io.iss_uops(w).prs1 := 0.U
    io.iss_uops(w).prs2 := 0.U
    io.iss_uops(w).prs3 := 0.U
    io.iss_uops(w).lrs1_rtype := RT_X
    io.iss_uops(w).lrs2_rtype := RT_X
  }

  val port_issued = Array.fill(issueWidth){false.B}
  // urgent_dlq > slots > crq
  val requests = (dlq_urgent zip dlq_request).map {case (a,b) => a && b} ++
    issue_slots.map(s => s.request)++
    io.crq_head.get.map(h => h.valid)++
    (dlq_urgent zip dlq_request).map {case (a,b) => !a && b}
  val grants = dlq_grant_urgent ++
    issue_slots.map(s => s.grant)++
    io.crq_head.get.map(h => h.ready)++
    dlq_grant
  val candidate_uops = dlq_uop++
    issue_slots.map(s => s.uop)++
    io.crq_head.get.map(h => h.bits)++
    dlq_uop

  val len = numIssueSlots + dnbParams.dlqDispatches*2 + dnbParams.crqDispatches

  require(requests.length == len)
  require(grants.length == len)
  require(candidate_uops.length == len)

  for (i <- 0 until len) {
    grants(i) := false.B
    var uop_issued = false.B

    for (w <- 0 until issueWidth) {
      val iq_type_match = (candidate_uops(i).iq_type === io.iq_types.get(w))
      val fu_type_match = ((candidate_uops(i).fu_code & io.fu_types(w)) =/= 0.U)
      iq_type_match.suggestName(s"iq_type_match_slot_${i}_exu_$w")
      fu_type_match.suggestName(s"fu_type_match_slot_${i}_exu_$w")
      val can_allocate = fu_type_match && iq_type_match

      when (requests(i) && !uop_issued && can_allocate && !port_issued(w)) {
        grants(i) := true.B
        io.iss_valids(w) := true.B
        io.iss_uops(w) := candidate_uops(i)
      }
      val was_port_issued_yet = port_issued(w)
      port_issued(w) = (requests(i) && !uop_issued && can_allocate) | port_issued(w)
      uop_issued = (requests(i) && can_allocate && !was_port_issued_yet) | uop_issued
    }
  }
}
