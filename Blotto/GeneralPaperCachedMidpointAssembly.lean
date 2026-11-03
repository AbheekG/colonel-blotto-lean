import Blotto.GeneralPaperRationalScalarStep
import Blotto.DyadicMidpointAssemblyCost

/-! Rational midpoint assembly reads the retained midpoint count; it never
reconstructs a denominator power. Every conversion/copy/arithmetic/result and
fixed source-reference/control step is charged with the actual data. -/
namespace Blotto.GeneralPaperCachedMidpointAssembly
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperRationalScalarStep
set_option autoImplicit false
set_option maxHeartbeats 700000

def height (K : ℕ) : ℕ := expressionHeightBudget (K + 2) 3

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A rank : ℕ) : ℚ × ℕ :=
  let index := natural A rank
  let count := natural A p.midpointCount
  let doubled := GeneralPaperRationalScalarStep.run model A .mul index.1 2
  let numerator := GeneralPaperRationalScalarStep.run model A .add doubled.1 1
  let denominator := GeneralPaperRationalScalarStep.run model A .mul 2 count.1
  let quotient := GeneralPaperRationalScalarStep.run model A .div numerator.1 denominator.1
  (quotient.1, index.2 + count.2 + doubled.2 + numerator.2 + denominator.2 + quotient.2)

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (bits : Fin p.midpointBits → Bool) :
    (run p model A (balancedBitIndex p.midpointBits bits).val).1 = GeneralPaperEqualPreparedCache.midpoint p bits := by
  simp only [run, natural, GeneralPaperRationalScalarStep.run, Op.apply, GeneralPaperEqualPreparedCache.midpoint, Nat.cast_mul]
  norm_num

theorem work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A rank : ℕ) (hr : rank < 2 ^ p.midpointBits) :
    (run p model A rank).2 ≤ 24 * model.rat (1 + 2 * height p.midpointBits) + 96 * A + 96 := by
  let L := p.midpointBits + 2
  let S := height p.midpointBits
  have hLS : L ≤ S := expressionHeightBudget_ge_input L 3
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hr' : rank < 2 ^ L := hr.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [L]; omega))
  have hn : p.midpointCount < 2 ^ L := by rw [p.midpointCount_correct]; exact Nat.pow_lt_pow_right (by decide) (by dsimp [L]; omega)
  have hR := DyadicMidpointAssembly.nat_height rank L (by omega) hr'
  have hN := DyadicMidpointAssembly.nat_height p.midpointCount L (by omega) hn
  have hOne : RationalHeight (1 : ℚ) L := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hL
  have hTwo : RationalHeight (2 : ℚ) L := (show RationalHeight (2 : ℚ) 2 by norm_num [RationalHeight]).mono hL
  have hD := hR.mul hTwo
  have hNum := hD.add hOne
  have hDen := hTwo.mul hN
  have hOut := hNum.div hDen
  have hSize : 5 * L + 1 ≤ S := by dsimp [S, height, expressionHeightBudget, L]; norm_num; omega
  have hD' := hD.mono (show L + L ≤ S by omega)
  have hNum' := hNum.mono (show L + L + L + 1 ≤ S by omega)
  have hDen' := hDen.mono (show L + L ≤ S by omega)
  have hOut' := hOut.mono (show L + L + L + 1 + (L + L) ≤ S by omega)
  have hc1 := natural_work model A rank S (hR.mono hLS)
    ((binaryWordWidth_le_of_lt_pow (by omega : 0 < L) hr').trans (by omega))
  have hc2 := natural_work model A p.midpointCount S (hN.mono hLS)
    ((binaryWordWidth_le_of_lt_pow (by omega : 0 < L) hn).trans (by omega))
  have hc3 := GeneralPaperRationalScalarStep.work model A .mul (rank : ℚ) 2 S (hR.mono hLS) (hTwo.mono hLS) hD'
  have hc4 := GeneralPaperRationalScalarStep.work model A .add ((rank : ℚ) * 2) 1 S hD' (hOne.mono hLS) hNum'
  have hc5 := GeneralPaperRationalScalarStep.work model A .mul 2 (p.midpointCount : ℚ) S (hTwo.mono hLS) (hN.mono hLS) hDen'
  have hc6 := GeneralPaperRationalScalarStep.work model A .div ((rank : ℚ) * 2 + 1) (2 * (p.midpointCount : ℚ)) S hNum' hDen' hOut'
  unfold run
  dsimp only [GeneralPaperRationalScalarStep.run, natural, Op.apply] at hc1 hc2 hc3 hc4 hc5 hc6 ⊢
  change _ ≤ 24 * model.rat (1 + 2 * S) + 96 * A + 96
  omega

end Blotto.GeneralPaperCachedMidpointAssembly
