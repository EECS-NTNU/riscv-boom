package boom.exu

import Chisel.{MuxCase, MuxLookup, PopCount, PriorityMux, Valid, log2Ceil}
import boom.common.BoomModule
import boom.util.{WrapAdd, WrapDec}
import chipsalliance.rocketchip.config.Parameters
import chisel3._

class ShadowBuffer(implicit p: Parameters) extends BoomModule {

  val io = new Bundle {
    val flush_in = Input(Bool())
    val br_mispred_shadow_buffer_idx = Input(Valid(UInt(log2Ceil(maxBrCount).W)))
    val release_queue_tail_checkpoint = Input(UInt(log2Ceil(numLdqEntries).W))
    val br_mispredict_release_queue_idx = Output(Valid(UInt(log2Ceil(numLdqEntries).W)))

    val new_branch_op = Input(Vec(coreWidth, Bool()))
    val new_ldq_op = Input(Vec(coreWidth, Bool()))
    val br_safe_in = Input(Vec(coreWidth, Valid(UInt(log2Ceil(maxBrCount).W))))

    val shadow_buffer_head_out = Output(UInt(log2Ceil(maxBrCount).W))
    val shadow_buffer_tail_out = Output(UInt(log2Ceil(maxBrCount).W))
    val shadow_buffer_full_out = Output(Bool())
  }

  def IsIndexBetweenHeadAndTail(Index: UInt, Head: UInt, Tail: UInt): Bool = {
    ((Head < Tail) && Index >= Head && Index < Tail) || ((Head > Tail) && (Index < Tail || Index >= Head))
  }

  //Remember: Head is oldest speculative op, Tail is newest speculative op
  val ShadowBufferHead = RegInit(UInt(log2Ceil(maxBrCount).W), 0.U)
  val ShadowBufferTail = RegInit(UInt(log2Ceil(maxBrCount).W), 0.U)

  val ShadowCaster = Reg(Vec(maxBrCount, Bool()))
  val ReleaseQueueIndex = Reg(Vec(maxBrCount, UInt(log2Ceil(numLdqEntries).W)))

  val update_release_queue = RegNext(io.br_mispred_shadow_buffer_idx.valid)
  val update_release_queue_idx = RegNext(ReleaseQueueIndex(io.br_mispred_shadow_buffer_idx.bits))

  io.shadow_buffer_head_out := ShadowBufferHead
  io.shadow_buffer_tail_out := ShadowBufferTail
  io.shadow_buffer_full_out := (ShadowBufferHead === ShadowBufferTail) && ShadowCaster(ShadowBufferHead)

  ShadowBufferTail := WrapAdd(ShadowBufferTail, PopCount(io.new_branch_op), maxBrCount)

  val ShadowCasterIsFalse = Wire(Vec(coreWidth, Bool()))
  val HeadIsNotTail = Wire(Vec(coreWidth, Bool()))
  val ShadowCasterNotIncrement = Wire(Vec(coreWidth, Bool()))

  for (w <- 0 until coreWidth) {
    ShadowCasterIsFalse(w) := ! ShadowCaster(WrapAdd(ShadowBufferHead, w.U, maxBrCount))
    HeadIsNotTail(w) := WrapAdd(ShadowBufferHead, w.U, maxBrCount) =/= ShadowBufferTail
    ShadowCasterNotIncrement(w) := !(ShadowCasterIsFalse(w) && HeadIsNotTail(w))
  }

  val incrementLevel = MuxCase(coreWidth.U, (0 until coreWidth).map(e => ShadowCasterNotIncrement(e) -> e.U))
  ShadowBufferHead := WrapAdd(ShadowBufferHead, incrementLevel, maxBrCount)

  dontTouch(ShadowCasterNotIncrement)
  dontTouch(ShadowCaster)
  dontTouch(incrementLevel)

  val branch_before = WireInit(VecInit(Seq.fill(coreWidth + 1)(false.B)))
  val masked_ldq = WireInit(VecInit(Seq.fill(coreWidth+1)(0.U(log2Ceil(numLdqEntries).W))))

  dontTouch(branch_before)
  dontTouch(masked_ldq)

  for (w <- 0 until coreWidth) {
    when(io.new_branch_op(w) || branch_before(w)) {
      branch_before(w+1) := true.B
    }
  }
  for (w <- 0 until coreWidth) {
    masked_ldq(w+1) := masked_ldq(w) + (io.new_ldq_op(w) && branch_before(w)).asUInt()
  }

  for (w <- 0 until coreWidth) {
    when(io.new_branch_op(w)) {
      ShadowCaster(WrapAdd(ShadowBufferTail, PopCount(io.new_branch_op.slice(0, w)), maxBrCount)) := true.B
      when(ShadowBufferHead =/= ShadowBufferTail) {
        ReleaseQueueIndex(WrapAdd(ShadowBufferTail, PopCount(io.new_branch_op.slice(0, w)), maxBrCount)) := WrapAdd(io.release_queue_tail_checkpoint, PopCount(io.new_ldq_op.slice(0, w)), numLdqEntries)
      }.otherwise {
        ReleaseQueueIndex(WrapAdd(ShadowBufferTail, PopCount(io.new_branch_op.slice(0, w)), maxBrCount)) := WrapAdd(io.release_queue_tail_checkpoint, masked_ldq(w) , numLdqEntries)
      }
    }

    when(io.br_safe_in(w).valid) {
      ShadowCaster(io.br_safe_in(w).bits) := false.B
    }
  }

  io.br_mispredict_release_queue_idx.valid := false.B
  io.br_mispredict_release_queue_idx.bits := update_release_queue_idx

  when(update_release_queue) {
    io.br_mispredict_release_queue_idx.valid := true.B
  }

  when(io.flush_in) {
    ShadowBufferHead := 0.U
    ShadowBufferTail := 0.U

    //TODO: Remove this
    for (w <- 0 until maxBrCount) {
      ShadowCaster(w) := false.B
    }
  }.elsewhen(io.br_mispred_shadow_buffer_idx.valid) {
    ShadowBufferTail := io.br_mispred_shadow_buffer_idx.bits

    //TODO: Remove this
    ShadowCaster(io.br_mispred_shadow_buffer_idx.bits) := false.B
    ReleaseQueueIndex(io.br_mispred_shadow_buffer_idx.bits) := 0.U

    //TODO: Remove this
    for (w <- 0 until maxBrCount) {
      when(IsIndexBetweenHeadAndTail(w.U, ShadowBufferHead, io.br_mispred_shadow_buffer_idx.bits)) {
        ShadowCaster(w) := false.B
      }
    }
  }

}