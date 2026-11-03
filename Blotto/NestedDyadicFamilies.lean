import Blotto.FirstDyadicApproximation
import Blotto.NestedFamily

/-! Fixed-mean nested family and explicit residual segment lottery, with
their finite scalar-draw laws and uniform CDF error bounds. -/

namespace Blotto
open MeasureTheory

namespace NestedInput

noncomputable def familyFirstDyadicLaw (i : NestedInput) (x : ℝ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) : Mixed 3 :=
  (i.atLength x hx0 (by linarith [i.lengths.2.2.1])).firstDyadicApproximation hxv K

theorem familyFirstDyadicLaw_CDF_error (i : NestedInput) (x : ℝ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) :
    CDFClose (i.familyFirstDyadicLaw x hx0 hxv K) (i.familyFirstLaw x hx0 hxv) (3 / (2 * (2 : ℝ) ^ K)) :=
  (i.atLength x hx0 (by linarith [i.lengths.2.2.1])).firstDyadicApproximation_CDF_error hxv K

theorem familyFirstDyadicLaw_fullBudget (i : NestedInput) (x : ℝ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) :
    ∀ᵐ y ∂(i.familyFirstDyadicLaw x hx0 hxv K : Measure (Allocation 3)), FullBudget i.M y :=
  (i.atLength x hx0 (by linarith [i.lengths.2.2.1])).firstDyadicApproximation_fullBudget hxv K

end NestedInput

namespace NestedResidual

noncomputable def segmentLottery (r : NestedResidual) : SegmentLottery 3 3 :=
  ⟨r.weight, (fun j => r.vertex (edges j).1), (fun j => r.vertex (edges j).2), r.weight_nonnegative, r.weight_mass⟩

theorem segmentLottery_law (r : NestedResidual) : r.segmentLottery.law = r.law := rfl

noncomputable def dyadicLaw (r : NestedResidual) (K : ℕ) : Mixed 3 := r.segmentLottery.dyadicLaw K

theorem dyadicLaw_CDF_error (r : NestedResidual) (K : ℕ) :
    CDFClose (r.dyadicLaw K) r.law (1 / (2 * (2 : ℝ) ^ K)) := r.segmentLottery.dyadicLaw_CDF_error K

theorem dyadicLaw_fullBudget (r : NestedResidual) (K : ℕ) :
    ∀ᵐ y ∂(r.dyadicLaw K : Measure (Allocation 3)), FullBudget r.g.budget y :=
  r.segmentLottery.dyadicLaw_fullBudget K (fun _j => ⟨r.vertex_fullBudget _, r.vertex_fullBudget _⟩)

end NestedResidual
end Blotto
