import Blotto.ThreeLottery
import Blotto.DyadicSegmentLottery

/-! All three-variable coupling cases have actual K-bit scalar draws with
uniform CDF error and exact budgets. Their component choice still uses the
exact weights; a capped fair-bit implementation of those choices is pending. -/

namespace Blotto
open MeasureTheory

namespace ThreeSpec

noncomputable def dyadicLaw (i : ThreeSpec) (K : ℕ) : Mixed 3 := i.segmentLottery.dyadicLaw K

theorem dyadicLaw_CDF_error (i : ThreeSpec) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (1 / (2 * (2 : ℝ) ^ K)) := by
  have he := i.segmentLottery.dyadicLaw_CDF_error K
  have hl : i.segmentLottery.law = i.law := ProbabilityMeasure.toMeasure_injective i.segmentLottery_law
  rw [hl] at he
  exact he

theorem dyadicLaw_fullBudget (i : ThreeSpec) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 3)), FullBudget i.B x :=
  i.segmentLottery.dyadicLaw_fullBudget K (fun j => ⟨i.segmentLottery_endpoints.1 j, i.segmentLottery_endpoints.2 j⟩)

theorem dyadicPoint_fullBudget (i : ThreeSpec) (K : ℕ) (edge : Fin 9) (bits : Fin K → Bool) :
    FullBudget i.B (i.segmentLottery.dyadicPoint K edge bits) :=
  i.segmentLottery.dyadicPoint_fullBudget K (fun j => ⟨i.segmentLottery_endpoints.1 j, i.segmentLottery_endpoints.2 j⟩) edge bits

end ThreeSpec
end Blotto
