package lsc

import boom.common.{BoomBundle, BoomModule, MicroOp}
import boom.exu.{BrResolutionInfo, BusyResp, CommitSignals}
import chisel3._
import chisel3.core.Bundle
import chisel3.util._
import freechips.rocketchip.config.Parameters

class IstIO(implicit p: Parameters) extends BoomBundle
{
  val mark = Input(new IstMark)
  val check = Flipped(Vec(coreWidth, DecoupledIO(UInt(vaddrBits.W)))) // use ready bit as reponse
}
class IstMark(implicit p: Parameters) extends BoomBundle
{
  val mark = Vec(retireWidth*2, ValidIO(UInt(vaddrBits.W)))
}

class InstructionSliceTable(entries: Int=128, ways: Int=2)(implicit p: Parameters) extends BoomModule{
  val io = IO(new IstIO())
  require(isPow2(entries))
  require(isPow2(ways))

  val tag_table = Reg(Vec(entries, UInt(vaddrBits.W)))
  val tag_valids = RegInit(VecInit(Seq.fill(entries)(false.B)))
  val tag_lru = RegInit(VecInit(Seq.fill(entries/2)(false.B)))

  def index(i: UInt): UInt ={
    i(log2Up(entries/ways)+2-1, 2) // ignore two lowest bits - 32word addrs even for compressed
  }
  require(ways == 2, "only one lru bit for now!")
  // check
  for(i <- 0 until coreWidth){
    val pc = io.check(i).bits
    val idx = index(pc)
    val is_match = WireInit(false.B)
    io.check(i).ready := is_match // true if pc in IST
    when(io.check(i).valid){
      for(j <- 0 until ways){
        val tidx = (idx << log2Up(ways)).asUInt() + j.U
        when(tag_valids(tidx) && tag_table(tidx) === pc){
          tag_lru(idx) := j.B // TODO: fix LRU hack
          is_match := true.B
        }
      }
    }
  }
  // mark - later so mark lrus get priority
  for(i <- 0 until retireWidth*2){
    when(io.mark.mark(i).valid){
      val pc = io.mark.mark(i).bits
      val idx = index(pc)
      val is_match = WireInit(false.B)
      for(j <- 0 until ways){
        val tidx = (idx << log2Up(ways)).asUInt() + j.U
        when(tag_valids(tidx) && tag_table(tidx) === pc){
          tag_lru(idx) := j.B // TODO: fix LRU hack
          is_match := true.B
        }
      }
      when(!is_match){
        tag_lru(idx) := !tag_lru(idx)
        val tidx = (idx << log2Up(ways)).asUInt() + !tag_lru(idx)
        tag_table(tidx) := pc
        tag_valids(tidx) := true.B
      }
    }
  }
}
