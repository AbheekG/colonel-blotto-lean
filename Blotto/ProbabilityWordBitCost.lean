import Blotto.ProbabilityWords
import Blotto.RationalCostModel

/-! Canonical rational-to-coin extraction reads and writes the actual integer
fields and checks the numerator tag. It performs no representation search or
new rational arithmetic. Allocation/address/backend costs are separate. -/

namespace Blotto.ProbabilityWords

def ofRatBitCost (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) : ℕ :=
  binaryWordWidth p.num.natAbs + binaryWordWidth p.den +
    binaryWordWidth (ofRat p hp).numerator + binaryWordWidth (ofRat p hp).denominator + 1

theorem nonnegative_abs_eq_toNat (p : ℚ) (hp : 0 ≤ p) : p.num.natAbs = p.num.toNat := by
  have he : (p.num.natAbs : ℤ) = (p.num.toNat : ℤ) :=
    (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hp)).trans
      (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hp)).symm
  exact_mod_cast he

theorem ofRatBitCost_eq (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ofRatBitCost p hp = 2 * rationalWordWidth p - 1 := by
  have hAbs := nonnegative_abs_eq_toNat p hp.1
  simp only [ofRatBitCost, ofRat, rationalWordWidth]
  rw [← hAbs]
  omega

theorem ofRatBitCost_bound (model : RationalCostModel) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (W : ℕ) (hW : rationalWordWidth p ≤ W) : ofRatBitCost p hp ≤ 2 * model.rat W := by
  have hw := hW.trans (model.word_le W)
  rw [ofRatBitCost_eq]
  omega

end Blotto.ProbabilityWords
