import Blotto.DyadicMidpointLaw

/-! Segment lotteries with their scalar draw implemented by K fair bits.
Component probabilities are still exact; capped branch-choice access is a
separate implementation obligation. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

namespace SegmentLottery

noncomputable def dyadicLaw {n k : ℕ} (l : SegmentLottery n k) (K : ℕ) : Mixed n :=
  probabilityMixture l.weight (fun i => dyadicSegmentLaw K (l.P i) (l.Q i)) l.nonnegative l.mass

noncomputable def dyadicPoint {n k : ℕ} (l : SegmentLottery n k) (K : ℕ) (i : Fin k)
    (bits : Fin K → Bool) : Allocation n := dyadicSegmentPoint K (l.P i) (l.Q i) bits

theorem dyadicLaw_eq_midpoint {n k : ℕ} (l : SegmentLottery n k) (K : ℕ) :
    l.dyadicLaw K = l.midpointLaw (pow_pos (by decide : 0 < (2 : ℕ)) K) := by
  have he : (fun i => dyadicSegmentLaw K (l.P i) (l.Q i)) =
      (fun i => midpointSegmentLaw (pow_pos (by decide : 0 < (2 : ℕ)) K) (l.P i) (l.Q i)) :=
    funext (fun i => dyadicSegmentLaw_eq K (l.P i) (l.Q i))
  unfold dyadicLaw
  rw [he]
  rfl

theorem dyadicLaw_CDF_error {n k : ℕ} (l : SegmentLottery n k) (K : ℕ) :
    CDFClose (l.dyadicLaw K) l.law (1 / (2 * (2 : ℝ) ^ K)) := by
  rw [l.dyadicLaw_eq_midpoint]
  have he := l.midpointLaw_CDF_error (pow_pos (by decide : 0 < (2 : ℕ)) K)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using he

theorem dyadicLaw_fullBudget {n k : ℕ} (l : SegmentLottery n k) (K : ℕ) {B : ℝ}
    (h : ∀ i, FullBudget B (l.P i) ∧ FullBudget B (l.Q i)) :
    ∀ᵐ x ∂(l.dyadicLaw K : Measure (Allocation n)), FullBudget B x := by
  rw [l.dyadicLaw_eq_midpoint]
  exact l.midpointLaw_fullBudget _ h

theorem dyadicPoint_fullBudget {n k : ℕ} (l : SegmentLottery n k) (K : ℕ) {B : ℝ}
    (h : ∀ i, FullBudget B (l.P i) ∧ FullBudget B (l.Q i)) (i : Fin k) (bits : Fin K → Bool) :
    FullBudget B (l.dyadicPoint K i bits) := dyadicSegmentPoint_fullBudget K (h i).1 (h i).2 bits

end SegmentLottery
end Blotto
