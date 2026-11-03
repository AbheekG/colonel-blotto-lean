import Blotto.RationalTerminalProfile
import Blotto.DyadicBoxes

/-! Exact terminal-law transport back to original coordinate order. The
outer location approximation keeps its CDF error after this permutation. -/

namespace Blotto
open MeasureTheory

theorem averaged_fairBit_affine {n m : ℕ} (K : ℕ) (law : (Fin K → Bool) → Mixed n)
    (f : AffineAllocation n m) :
    averagedLaw (fairBitLaw K) (fun bits => (law bits).map f.value) (measurable_of_countable _) =
      (averagedLaw (fairBitLaw K) law (measurable_of_countable _)).map f.value := by
  apply ProbabilityMeasure.toMeasure_injective
  change (fairBitLaw K : Measure (Fin K → Bool)).bind
    (fun bits => Measure.map f.value (law bits : Measure (Allocation n))) =
    Measure.map f.value ((fairBitLaw K : Measure (Fin K → Bool)).bind (fun bits => (law bits : Measure (Allocation n))))
  exact (map_bind_family _ _ (measurable_of_countable _) f.value f.measurable).symm

namespace RationalTerminalResources

noncomputable def locationLaw (i : RationalTerminalResources) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.profile K bits).real.law) (measurable_of_countable _)

theorem locationLaw_eq (i : RationalTerminalResources) (K : ℕ) :
    i.locationLaw K = permuteLaw i.permutation (i.input.locationLaw K) := by
  have hf : (RationalAffineAllocation.permutation i.permutation).real.value = permuteAllocation i.permutation :=
    funext (RationalAffineAllocation.permutation_real i.permutation)
  calc
    _ = averagedLaw (fairBitLaw K) (fun bits =>
      ((i.input.profile K bits).real.law).map (RationalAffineAllocation.permutation i.permutation).real.value)
      (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro bits
        exact RationalSegmentLottery.mapped_law _ _
    _ = _ := by
      rw [averaged_fairBit_affine, hf]
      rfl

theorem locationLaw_CDF_error (i : RationalTerminalResources) (K : ℕ) :
    CDFClose (i.locationLaw K) i.real.law (1 / (2 : ℝ) ^ K) := by
  rw [i.locationLaw_eq]
  have h := permuteLaw_CDFClose (i.input.locationLaw_CDF_error K) i.permutation
  simpa only [i.input_real, i.permutation_real, TerminalResources.law] using h

noncomputable def midpointLaw (i : RationalTerminalResources) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.profile K bits).real.dyadicLaw K) (measurable_of_countable _)

theorem midpointLaw_CDF_error (i : RationalTerminalResources) (K : ℕ) :
    CDFClose (i.midpointLaw K) i.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := (profiled_midpoint_CDF_error K (i.profile K)).triangle (i.locationLaw_CDF_error K)
  have hsum : 1 / (2 * (2 : ℝ) ^ K) + 1 / (2 : ℝ) ^ K = 3 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

theorem midpointLaw_fullBudget (i : RationalTerminalResources) (K : ℕ) :
    ∀ᵐ x ∂(i.midpointLaw K : Measure (Allocation 3)), FullBudget (i.M : ℝ) x := by
  apply averagedLaw_fullBudget
  exact Filter.Eventually.of_forall (fun bits => (i.profile K bits).real.dyadicLaw_fullBudget K (i.profile_endpoints K bits))

theorem midpointLaw_inBox (i : RationalTerminalResources) (K : ℕ) :
    ∀ᵐ x ∂(i.midpointLaw K : Measure (Allocation 3)), InBox (fun j => (i.long j : ℝ)) x := by
  apply bind_ae_family _ _ (measurable_of_countable _) (measurable_inBox _)
  exact Filter.Eventually.of_forall (fun bits => (i.profile K bits).real.dyadicLaw_inBox K (i.profile_box K bits))

end RationalTerminalResources
end Blotto
