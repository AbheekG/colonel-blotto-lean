import Blotto.NestedDyadicFamilies
import Blotto.NestedCoupling

/-! The second and third nested cases retain the first-case dyadic bound.
All mixing probabilities stay exact, including omitted zero-weight branches. -/

namespace Blotto.NestedInput
open MeasureTheory

noncomputable def secondUniformDyadicLaw (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) (K : ℕ) : Mixed 3 :=
  shiftedLaw i.mirrorLength ((i.secondUniformInput htu hTt).segmentLottery.dyadicLaw K)

theorem secondUniformDyadicLaw_CDF_error (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) (K : ℕ) :
    CDFClose (i.secondUniformDyadicLaw htu hTt K) (i.secondUniformLaw htu hTt) (3 / (2 * (2 : ℝ) ^ K)) := by
  have he := (i.secondUniformInput htu hTt).segmentLottery.dyadicLaw_CDF_error K
  have hl : (i.secondUniformInput htu hTt).segmentLottery.law = (i.secondUniformInput htu hTt).couplingLaw :=
    ProbabilityMeasure.toMeasure_injective ((i.secondUniformInput htu hTt).segmentLottery_law)
  rw [hl] at he
  exact (shiftedLaw_CDFClose he i.mirrorLength).mono (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))

theorem secondUniformDyadicLaw_fullBudget (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) (K : ℕ) :
    ∀ᵐ y ∂(i.secondUniformDyadicLaw htu hTt K : Measure (Allocation 3)), FullBudget i.M y := by
  have he := (i.secondUniformInput htu hTt).segmentLottery_endpoints
  have hb : (i.secondUniformInput htu hTt).B + i.mirrorLength = i.M := by dsimp [secondUniformInput]; ring
  have hu := (i.secondUniformInput htu hTt).segmentLottery.dyadicLaw_fullBudget K (fun j => ⟨he.1 j, he.2 j⟩)
  simpa only [secondUniformDyadicLaw, hb] using shiftedLaw_fullBudget (le_of_lt (i.mirrorLength_bounds htu).1) hu

noncomputable def secondDyadicLaw (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) : Mixed 3 :=
  if hTt : i.mirrorLength < i.t then
    binaryLaw i.secondAlpha ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩
      (i.familyFirstDyadicLaw i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K)
      (i.secondUniformDyadicLaw htu hTt K)
  else i.familyFirstDyadicLaw i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K

theorem secondDyadicLaw_CDF_error (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) :
    CDFClose (i.secondDyadicLaw htu K) (i.secondLaw htu) (3 / (2 * (2 : ℝ) ^ K)) := by
  unfold secondDyadicLaw secondLaw
  split_ifs with hTt
  · exact binaryLaw_CDFClose _ _ (i.familyFirstDyadicLaw_CDF_error _ _ _ K) (i.secondUniformDyadicLaw_CDF_error htu hTt K)
  · exact i.familyFirstDyadicLaw_CDF_error _ _ _ K

theorem secondDyadicLaw_fullBudget (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) :
    ∀ᵐ y ∂(i.secondDyadicLaw htu K : Measure (Allocation 3)), FullBudget i.M y := by
  unfold secondDyadicLaw
  split_ifs with hTt
  · exact binaryLaw_fullBudget _ _ _ _ (i.familyFirstDyadicLaw_fullBudget _ _ _ K) (i.secondUniformDyadicLaw_fullBudget htu hTt K)
  · exact i.familyFirstDyadicLaw_fullBudget _ _ _ K

noncomputable def thirdDyadicLaw (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) : Mixed 3 :=
  if hv : 0 < i.v then
    binaryLaw i.thirdAlpha ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
      (i.familyFirstDyadicLaw i.v hv le_rfl K) ((i.residualInput hvt htu).dyadicLaw K)
  else (i.residualInput hvt htu).dyadicLaw K

theorem thirdDyadicLaw_CDF_error (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) :
    CDFClose (i.thirdDyadicLaw hvt htu K) (i.thirdLaw hvt htu) (3 / (2 * (2 : ℝ) ^ K)) := by
  have hr := ((i.residualInput hvt htu).dyadicLaw_CDF_error K).mono
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))
  unfold thirdDyadicLaw thirdLaw
  split_ifs with hv
  · exact binaryLaw_CDFClose _ _ (i.familyFirstDyadicLaw_CDF_error _ _ _ K) hr
  · exact hr

theorem thirdDyadicLaw_fullBudget (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) :
    ∀ᵐ y ∂(i.thirdDyadicLaw hvt htu K : Measure (Allocation 3)), FullBudget i.M y := by
  have hr := (i.residualInput hvt htu).dyadicLaw_fullBudget K
  have hb : (i.residualInput hvt htu).g.budget = i.M := i.geometry_matches.2.2.2
  rw [hb] at hr
  unfold thirdDyadicLaw
  split_ifs with hv
  · exact binaryLaw_fullBudget _ _ _ _ (i.familyFirstDyadicLaw_fullBudget _ _ _ K) hr
  · exact hr

end Blotto.NestedInput
