import Blotto.NestedFirst
import Blotto.ThreeLottery
import Blotto.DyadicSegmentLottery
import Blotto.AllocationCDFDistance

/-! Every first-case conditional law has a K-bit scalar-draw version. This
includes the zero-probability corner and arbitrary inactive component slots. -/

namespace Blotto.NestedInput
open MeasureTheory Set

noncomputable def firstConditionalDyadicLaw (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) (K : ℕ) : Mixed 3 := by
  classical
  exact if hs : s ∈ i.positiveParameters then
    shiftedLaw s ((i.firstGeometry htv s hs.1 hs.2).segmentLottery.dyadicLaw K)
  else dyadicSegmentLaw K ![0, i.d, s] ![i.a, 0, s]

theorem firstConditionalDyadicLaw_CDF_error (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) (K : ℕ) :
    CDFClose (i.firstConditionalDyadicLaw htv s K) (i.firstConditionalLaw htv s) (1 / (2 * (2 : ℝ) ^ K)) := by
  classical
  unfold firstConditionalDyadicLaw firstConditionalLaw
  split_ifs with hs
  · have he := (i.firstGeometry htv s hs.1 hs.2).segmentLottery.dyadicLaw_CDF_error K
    have hl : (i.firstGeometry htv s hs.1 hs.2).segmentLottery.law =
        (i.firstGeometry htv s hs.1 hs.2).couplingLaw :=
      ProbabilityMeasure.toMeasure_injective ((i.firstGeometry htv s hs.1 hs.2).segmentLottery_law)
    rw [hl] at he
    exact shiftedLaw_CDFClose he s
  · exact dyadicSegmentLaw_CDF_error K _ _

theorem firstConditionalDyadicLaw_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : s ∈ Icc 0 i.t) (K : ℕ) :
    ∀ᵐ x ∂(i.firstConditionalDyadicLaw htv s K : Measure (Allocation 3)), FullBudget i.M x := by
  classical
  unfold firstConditionalDyadicLaw
  split_ifs with hp
  · have he := (i.firstGeometry htv s hp.1 hp.2).segmentLottery_endpoints
    have hb : (i.firstGeometry htv s hp.1 hp.2).budget + s = i.M := by
      linarith [(i.firstGeometry_matches htv s hp.1 hp.2).2.2.2.1]
    have ht := (i.firstGeometry htv s hp.1 hp.2).segmentLottery.dyadicLaw_fullBudget K
      (fun j => ⟨he.1 j, he.2 j⟩)
    simpa only [hb] using shiftedLaw_fullBudget hs.1 ht
  · have hz : i.conditionalProbability s = 0 := by
      have hb := i.conditional_bounds htv hs
      have hn : ¬0 < i.conditionalProbability s := fun h => hp ⟨hs, h⟩
      linarith
    have he := i.conditional_zero htv hs hz
    rw [dyadicSegmentLaw_eq]
    exact midpointSegmentLaw_fullBudget _
      (fullBudget_three (le_rfl) (le_of_lt i.d_pos) hs.1 (by linarith [he.2.2.2]))
      (fullBudget_three (le_of_lt i.a_pos) (le_rfl) hs.1 (by linarith [he.2.2.1]))

noncomputable def firstConditionalDyadicPoint (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) (K : ℕ)
    (slot : Fin 9) (bits : Fin K → Bool) : Allocation 3 := by
  classical
  exact if hs : s ∈ i.positiveParameters then
    shiftThird s ((i.firstGeometry htv s hs.1 hs.2).segmentLottery.dyadicPoint K slot bits)
  else dyadicSegmentPoint K ![0, i.d, s] ![i.a, 0, s] bits

theorem firstConditionalDyadicPoint_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : s ∈ Icc 0 i.t) (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) :
    FullBudget i.M (i.firstConditionalDyadicPoint htv s K slot bits) := by
  classical
  unfold firstConditionalDyadicPoint
  split_ifs with hp
  · have he := (i.firstGeometry htv s hp.1 hp.2).segmentLottery_endpoints
    have hb : (i.firstGeometry htv s hp.1 hp.2).budget + s = i.M := by
      linarith [(i.firstGeometry_matches htv s hp.1 hp.2).2.2.2.1]
    have ht := (i.firstGeometry htv s hp.1 hp.2).segmentLottery.dyadicPoint_fullBudget K
      (fun j => ⟨he.1 j, he.2 j⟩) slot bits
    simpa only [hb] using shiftThird_fullBudget hs.1 ht
  · have hz : i.conditionalProbability s = 0 := by
      have hb := i.conditional_bounds htv hs
      have hn : ¬0 < i.conditionalProbability s := fun h => hp ⟨hs, h⟩
      linarith
    have he := i.conditional_zero htv hs hz
    exact dyadicSegmentPoint_fullBudget K
      (fullBudget_three (le_rfl) (le_of_lt i.d_pos) hs.1 (by linarith [he.2.2.2]))
      (fullBudget_three (le_of_lt i.a_pos) (le_rfl) hs.1 (by linarith [he.2.2.1])) bits

end Blotto.NestedInput
