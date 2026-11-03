import Blotto.RationalCoin

/-! The exhausted-prefix event of one rational coin has at most one bit
vector. Its actual probability under fresh fair inputs is at most 2^-K.
This is a one-coin bound; the adaptive shared-cap bound is still separate. -/

namespace Blotto
open MeasureTheory Set

theorem runRationalCoin_failure_probability (K : ℕ) (p : ℚ) :
    (fairBitLaw K : Measure (Fin K → Bool)).real {bits | (runRationalCoin K p bits).1 = none} ≤ 1 / (2 : ℝ) ^ K := by
  classical
  let A : Set (Fin K → Bool) := {bits | (runRationalCoin K p bits).1 = none}
  by_cases hA : A.Nonempty
  · rcases hA with ⟨bits, hbits⟩
    have hsub : A ⊆ {bits} := by
      intro x hx
      exact runRationalCoin_none_unique K p x bits hx hbits
    have hm := measureReal_mono (μ := (fairBitLaw K : Measure (Fin K → Bool))) hsub
    have he : (fairBitLaw K : Measure (Fin K → Bool)).real {bits} = 1 / (2 : ℝ) ^ K := by
      rw [Measure.real, fairBitLaw_singleton_realWeight, ENNReal.toReal_ofReal (by positivity)]
    exact hm.trans (le_of_eq he)
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    change (fairBitLaw K : Measure (Fin K → Bool)).real A ≤ _
    rw [he, measureReal_empty]
    positivity

end Blotto
