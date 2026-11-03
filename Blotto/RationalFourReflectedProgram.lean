import Blotto.RationalFourMidpoint
import Blotto.RationalNestedResourceProgram
import Blotto.RationalAffineBoxes

/-! Actual bounded native sampling of the reflected/zero-fourth component.
The resource and segment choices share one cap; reflection preserves every
output's budget and coordinate box, and the stated marginal CDF error. -/

namespace Blotto.RationalFourInput
open MeasureTheory

def reflectedSample (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) : Fin 4 → ℚ :=
  (RationalAffineAllocation.reflectAppend i.originalLengths).value ((i.reflectedResourceSystem hcase).sample K bits)

noncomputable def reflectedSampleLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalNestedResourceSystem.sampleBitBudget K)).map (fun bits j => (i.reflectedSample hcase K bits j : ℝ))

theorem reflectedSample_fullBudget (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.reflectedSample hcase K bits j : ℝ)) := by
  rw [reflectedSample, RationalAffineAllocation.value_real]
  have h := (i.reflectedResourceSystem hcase).sample_contract K bits
  exact RationalAffineAllocation.reflectAppend_fullBudget i.originalLengths (i.reflection_budget_sum hcase) h.1 h.2

theorem reflectedSample_inBox (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) :
    InBox ![(i.u : ℝ), (i.v : ℝ), (i.w : ℝ), (i.ell : ℝ)] (fun j => (i.reflectedSample hcase K bits j : ℝ)) := by
  rw [reflectedSample, RationalAffineAllocation.value_real]
  exact RationalAffineAllocation.reflectAppend_box i.originalLengths
    (by exact_mod_cast le_of_lt i.ell_pos) ((i.reflectedResourceSystem hcase).sample_contract K bits).2

theorem reflectedSampleLaw_eq (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    i.reflectedSampleLaw hcase K = reflectedLaw (fun j => (i.originalLengths j : ℝ))
      ((i.reflectedResourceSystem hcase).sampleLaw K) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits j => (i.reflectedSample hcase K bits j : ℝ))
    (fairBitLaw (RationalNestedResourceSystem.sampleBitBudget K) : Measure (Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool)) =
    Measure.map (reflectAppend (fun j => (i.originalLengths j : ℝ)))
      (Measure.map (fun bits j => ((i.reflectedResourceSystem hcase).sample K bits j : ℝ))
        (fairBitLaw (RationalNestedResourceSystem.sampleBitBudget K) : Measure (Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool)))
  rw [Measure.map_map (measurable_reflectAppend _) (measurable_of_countable _)]
  congr 1
  funext bits
  rw [reflectedSample, RationalAffineAllocation.value_real, RationalAffineAllocation.reflectAppend_real]
  rfl

theorem reflectedSampleLaw_CDF_error (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.reflectedSampleLaw hcase K) (i.real.reflectedZeroLaw (i.smallCase_real hcase)) (5 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.reflectedSampleLaw_eq]
  have h := (i.reflectedResourceSystem hcase).sampleLaw_CDF_error K
  rw [i.reflectedResourceSystem_real] at h
  have hR := reflectedLaw_CDFClose (fun j => (i.originalLengths j : ℝ)) h
  simpa only [i.originalLengths_real, FourInput.reflectedZeroLaw] using hR

end Blotto.RationalFourInput
