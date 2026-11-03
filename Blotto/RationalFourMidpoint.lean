import Blotto.RationalFourResources
import Blotto.RationalNestedResourceLaw
import Blotto.RationalMergeFourProgram
import Blotto.FourDyadicTransport

/-! The native four-variable atom-conditioning branch at its ideal midpoint
stage. Component probabilities remain exact here; one shared-cap continuation
controller is a separate operational step. -/

namespace Blotto.RationalFourInput
open MeasureTheory
open scoped BigOperators

noncomputable def uniformMidpointLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) : Mixed 4 :=
  (i.smallUniformLottery hcase).real.dyadicLaw K

theorem uniformMidpointLaw_CDF_error (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.uniformMidpointLaw hcase K) (i.real.smallUniformLaw (i.smallCase_real hcase)) (1 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.smallUniformLottery hcase).real.dyadicLaw_CDF_error K
  rw [i.smallUniformLottery_law] at h
  exact h

noncomputable def reflectedMidpointLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) : Mixed 4 :=
  ((i.reflectedResourceSystem hcase).midpointLaw K).map (RationalAffineAllocation.reflectAppend i.originalLengths).real.value

theorem reflectedMidpointLaw_eq (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    i.reflectedMidpointLaw hcase K = reflectedLaw (fun j => (i.originalLengths j : ℝ))
      ((i.reflectedResourceSystem hcase).midpointLaw K) := by
  unfold reflectedMidpointLaw reflectedLaw
  congr 1
  exact funext (RationalAffineAllocation.reflectAppend_real i.originalLengths)

theorem reflectedMidpointLaw_CDF_error (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.reflectedMidpointLaw hcase K) (i.real.reflectedZeroLaw (i.smallCase_real hcase)) (3 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.reflectedMidpointLaw_eq]
  have h := (i.reflectedResourceSystem hcase).midpointLaw_CDF_error K
  rw [i.reflectedResourceSystem_real] at h
  have hR := reflectedLaw_CDFClose (fun j => (i.originalLengths j : ℝ)) h
  simpa only [i.originalLengths_real, FourInput.reflectedZeroLaw] using hR

theorem reflection_budget_sum (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (∑ j, (i.originalLengths j : ℝ)) = (i.B : ℝ) + (i.reflectedBudget : ℝ) := by
  have hs : (∑ j, (i.originalLengths j : ℝ)) = (i.S : ℝ) := by exact_mod_cast i.originalLengths_sum
  rw [hs, (i.reflected_budget_bounds hcase).2, Rat.cast_sub]
  ring

theorem reflectedMidpointLaw_fullBudget (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    ∀ᵐ x ∂(i.reflectedMidpointLaw hcase K : Measure (Allocation 4)), FullBudget (i.B : ℝ) x := by
  rw [i.reflectedMidpointLaw_eq]
  exact reflectedLaw_fullBudget _ _ (i.reflection_budget_sum hcase)
    ((i.reflectedResourceSystem hcase).midpointLaw_fullBudget K) ((i.reflectedResourceSystem hcase).midpointLaw_inBox K)

noncomputable def smallMidpointLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) : Mixed 4 :=
  binaryLaw (i.p : ℝ) (by exact_mod_cast (show 0 ≤ i.p ∧ i.p ≤ 1 from ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩))
    (i.uniformMidpointLaw hcase K) (i.reflectedMidpointLaw hcase K)

theorem smallMidpointLaw_CDF_error (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.smallMidpointLaw hcase K) (i.real.smallCaseLaw (i.smallCase_real hcase)) (3 / (2 * (2 : ℝ) ^ K)) := by
  apply binaryLaw_CDFClose
  · exact (i.uniformMidpointLaw_CDF_error hcase K).mono
      (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))
  · exact i.reflectedMidpointLaw_CDF_error hcase K

theorem smallMidpointLaw_fullBudget (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    ∀ᵐ x ∂(i.smallMidpointLaw hcase K : Measure (Allocation 4)), FullBudget (i.B : ℝ) x := by
  apply binaryLaw_fullBudget
  · exact (i.smallUniformLottery hcase).real.dyadicLaw_fullBudget K (i.smallUniformLottery_endpoints hcase)
  · exact i.reflectedMidpointLaw_fullBudget hcase K

end Blotto.RationalFourInput
