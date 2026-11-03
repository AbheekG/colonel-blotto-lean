import Blotto.RationalNestedSpecProgram

/-! The nested ideal midpoint stage and its separate shared-cap error.
Keeping these errors separate permits composition with the global PRG cap. -/

namespace Blotto
open MeasureTheory

theorem profiled_midpoint_CDF_error {n k : ℕ} (K : ℕ)
    (profile : (Fin K → Bool) → RationalSegmentLottery n k) :
    CDFClose (averagedLaw (fairBitLaw K) (fun bits => (profile bits).real.dyadicLaw K) (measurable_of_countable _))
      (averagedLaw (fairBitLaw K) (fun bits => (profile bits).real.law) (measurable_of_countable _))
      (1 / (2 * (2 : ℝ) ^ K)) := by
  rw [averaged_fairBit_finite, averaged_fairBit_finite]
  apply probabilityMixture_CDFClose
  intro scalarIndex
  exact (profile ((bitIndexEquiv K).symm scalarIndex)).real.dyadicLaw_CDF_error K

theorem profiled_cap_midpoint_CDF_error {n k : ℕ} (K : ℕ) (fallback : Fin k)
    (profile : (Fin K → Bool) → RationalSegmentLottery n k) :
    CDFClose (averagedLaw (fairBitLaw K) (fun bits => (profile bits).flatLaw fallback (3 * (k - 1 + K)) K) (measurable_of_countable _))
      (averagedLaw (fairBitLaw K) (fun bits => (profile bits).real.dyadicLaw K) (measurable_of_countable _))
      (1 / (2 : ℝ) ^ K) := by
  rw [averaged_fairBit_finite, averaged_fairBit_finite]
  apply probabilityMixture_CDFClose
  intro scalarIndex
  rw [RationalSegmentLottery.flatLaw_eq]
  exact (profile ((bitIndexEquiv K).symm scalarIndex)).cappedLaw_midpoint_CDF_error fallback K K

namespace RationalNestedInput

noncomputable def midpointLaw (i : RationalNestedInput) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.profile K bits).real.dyadicLaw K) (measurable_of_countable _)

theorem midpointLaw_CDF_error (i : RationalNestedInput) (K : ℕ) :
    CDFClose (i.midpointLaw K) i.real.couplingLaw (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := (profiled_midpoint_CDF_error K (i.profile K)).triangle (i.locationLaw_CDF_error K)
  have hsum : 1 / (2 * (2 : ℝ) ^ K) + 1 / (2 : ℝ) ^ K = 3 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

theorem sampleLaw_midpoint_CDF_error (i : RationalNestedInput) (K : ℕ) :
    CDFClose (i.sampleLaw K) (i.midpointLaw K) (1 / (2 : ℝ) ^ K) := by
  rw [i.sampleLaw_average]
  exact profiled_cap_midpoint_CDF_error K 0 (i.profile K)

end RationalNestedInput

namespace RationalNestedSpec

noncomputable def midpointLaw (i : RationalNestedSpec) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.profile K bits).real.dyadicLaw K) (measurable_of_countable _)

theorem midpointLaw_CDF_error (i : RationalNestedSpec) (K : ℕ) :
    CDFClose (i.midpointLaw K) i.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := (profiled_midpoint_CDF_error K (i.profile K)).triangle (i.locationLaw_CDF_error K)
  have hsum : 1 / (2 * (2 : ℝ) ^ K) + 1 / (2 : ℝ) ^ K = 3 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

theorem sampleLaw_midpoint_CDF_error (i : RationalNestedSpec) (K : ℕ) :
    CDFClose (i.sampleLaw K) (i.midpointLaw K) (1 / (2 : ℝ) ^ K) := by
  rw [i.sampleLaw_average]
  exact profiled_cap_midpoint_CDF_error K 0 (i.profile K)

end RationalNestedSpec
end Blotto
