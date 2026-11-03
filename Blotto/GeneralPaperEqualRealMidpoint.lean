import Blotto.GeneralPaperRealCumulativeChoiceLaw
import Blotto.GeneralPaperNativeDyadicBlocks
import Blotto.GeneralPaperNativeFreshBuffer

/-! Real-model midpoint production uses one fresh K-bit buffer, a forward
addition/doubling decoder and four scalar operations with the stored midpoint
count. Source read/index/write/control prices are included at unit price. -/
namespace Blotto.GeneralPaperEqualRealMidpoint
open GeneralPaperEqualPreparedCache
open PRGRealRAMExecution
set_option autoImplicit false
set_option maxHeartbeats 700000

structure Result where
  value : ℝ
  reads : ℕ
  work : ℕ

noncomputable def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (fresh : Fin p.midpointBits → Bool) : Result :=
  let buffer := GeneralPaperNativeFreshBuffer.run (fun _ => 1) 1 fresh
  let rank := GeneralPaperNativeFairIndex.loop (fun _ => 1) 1 buffer.1.1 0 p.midpointBits
    (by omega) p.midpointBits le_rfl
  let doubled := arithmetic .mul (rank.value : ℝ) 2
  let numerator := arithmetic .add doubled.value 1
  let denominator := arithmetic .mul 2 (p.midpointCount : ℝ)
  let quotient := arithmetic .div numerator.value denominator.value
  ⟨quotient.value, buffer.1.2,
    buffer.2 + rank.work + doubled.cost + numerator.cost + denominator.cost + quotient.cost + 16⟩

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (fresh : Fin p.midpointBits → Bool) :
    (run p fresh).value = (GeneralPaperEqualPreparedCache.midpoint p fresh : ℝ) := by
  have hd := GeneralPaperNativeDyadicBlocks.block_data (fun _ => 1) 1 0 p.midpointBits (by omega) fresh
  have hh : (fun j : Fin p.midpointBits => fresh ⟨0 + j.val, by omega⟩) = fresh := by
    funext j
    congr 1
    exact Fin.ext (Nat.zero_add j.val)
  rw [hh] at hd
  unfold run
  dsimp only
  rw [GeneralPaperNativeFreshBuffer.run_data, hd]
  simp only [arithmetic, Operation.realValue, RealArithmeticOp.apply, GeneralPaperEqualPreparedCache.midpoint, balancedBitIndex_eq,
    Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, Nat.cast_mul]
  norm_num

theorem reads {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (fresh : Fin p.midpointBits → Bool) : (run p fresh).reads = p.midpointBits :=
  GeneralPaperNativeFreshBuffer.run_reads _ _ _

theorem work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (fresh : Fin p.midpointBits → Bool) : (run p fresh).work ≤ 144 * p.midpointBits + 116 := by
  have hb := GeneralPaperNativeFreshBuffer.arithmetic_work 1 fresh
  have hr := GeneralPaperNativeFairIndex.arithmetic_work 1
    (GeneralPaperNativeFreshBuffer.run (fun _ => 1) 1 fresh).1.1 0 p.midpointBits (by omega) p.midpointBits le_rfl
  unfold run
  dsimp only
  simp only [arithmetic, Run.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Operation.cost]
  nlinarith only [hb, hr]

end Blotto.GeneralPaperEqualRealMidpoint
