import Blotto.SignedLatticeSize
import Blotto.RationalHeight

/-! Unit-box rationals on the common input denominator have individual
numerator/denominator height bounded by that denominator's word width. -/

namespace Blotto

theorem rationalHeight_unit_lattice {D : ℕ} (hD : 0 < D) {q : ℚ}
    (hQ : OnRationalLattice D q) (hBox : 0 ≤ q ∧ q ≤ 1) : RationalHeight q (binaryWordWidth D) := by
  have hAbs : |q| ≤ (1 : ℚ) := by rw [abs_of_nonneg hBox.1]; exact hBox.2
  have hNum := rationalLattice_abs_numerator_le (M := 1) hD hQ hAbs
  simp only [one_mul] at hNum
  exact ⟨hNum.trans_lt (lt_pow_binaryWordWidth D),
    (rationalLattice_den_le hD hQ).trans_lt (lt_pow_binaryWordWidth D)⟩

end Blotto
