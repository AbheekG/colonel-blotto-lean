import Blotto.RationalSegmentProgram

/-! Exact measurable-event probabilities of a descriptor at a fixed scalar
block. This links the categorical controller mean to the allocation law. -/

namespace Blotto.RationalSegmentLottery
open MeasureTheory
open scoped BigOperators Classical

theorem fixedIdeal_event {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ)
    (bits : Fin K → Bool) (A : Set (Allocation n)) (hA : MeasurableSet A) :
    (l.fixedIdeal K bits : Measure (Allocation n)).real A =
      ∑ slot, (l.weight slot : ℝ) * (if (fun j => (l.point K slot bits j : ℝ)) ∈ A then (1 : ℝ) else 0) := by
  unfold fixedIdeal
  rw [probabilityMixture_real_apply _ _ _ _ _ hA]
  apply Finset.sum_congr rfl
  intro slot _
  by_cases hs : (fun j => (l.point K slot bits j : ℝ)) ∈ A <;>
    simp [real, allocationPointLaw, Measure.real, Measure.dirac_apply' _ hA, hs]

end Blotto.RationalSegmentLottery
