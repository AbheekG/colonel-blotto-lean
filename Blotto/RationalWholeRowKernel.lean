import Blotto.ProductFiniteTraining

/-! A finite rational whole-law expectation kernel and its actual probability
measure event identity. Labels are proof representations; these definitions
do not provide a runtime enumeration of the constrained product support. -/

namespace Blotto.RationalWholeRowLaw
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def rowKernel {r m : ℕ} (law : RationalWholeRowLaw r m) :
    BoundedExpectationKernel (Fin m → ℚ) where
  mean := fun test => ∑ i, law.realWeight i * test (law.row i)
  constant := by
    intro c
    rw [← Finset.sum_mul, law.realWeight_sum, one_mul]
  monotone := by
    intro f g h
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h _) (law.realWeight_nonnegative i)
  add := by intro f g; simp only [mul_add, Finset.sum_add_distrib]

theorem rowKernel_event {r m : ℕ} (law : RationalWholeRowLaw r m)
    (event : Set (Allocation m)) (hEvent : MeasurableSet event) :
    law.rowKernel.mean (fun row => if (fun field => (row field : ℝ)) ∈ event then 1 else 0) =
      (law.law : Measure (Allocation m)).real event := by
  exact (law.law_event event hEvent).symm

end Blotto.RationalWholeRowLaw
