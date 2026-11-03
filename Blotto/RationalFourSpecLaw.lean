import Blotto.RationalFourSpecMachine

/-! Normalized-controller ideal-law linkage for the global shared-cap
compiler, with the same midpoint error in original coordinate order. -/

namespace Blotto.RationalFourSpec
open MeasureTheory

noncomputable def midpointLaw (i : RationalFourSpec) (K : ℕ) : Mixed 4 :=
  permuteLaw i.permutation (i.input.midpointLaw K)

theorem midpointLaw_CDF_error (i : RationalFourSpec) (K : ℕ) :
    CDFClose (i.midpointLaw K) i.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := permuteLaw_CDFClose (i.input.midpointLaw_CDF_error K) i.permutation
  simpa only [midpointLaw, i.input_real, i.permutation_real, FourSpec.law] using h

noncomputable def fixedIdealLaw (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : Mixed 4 :=
  (i.machine K outerBits scalarBits).rationalIdealLaw (i.input.start K outerBits scalarBits)

theorem fixedIdealLaw_eq (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.fixedIdealLaw K outerBits scalarBits = (i.input.fixedIdealLaw K outerBits scalarBits).map
      (RationalAffineAllocation.permutation i.permutation).real.value := by
  unfold fixedIdealLaw machine
  rw [WordStateMachine.rationalIdealLaw_mapped]
  rfl

theorem averaged_fixedIdeal (i : RationalFourSpec) (K : ℕ) :
    averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => i.fixedIdealLaw K outerBits scalarBits) (measurable_of_countable _)) (measurable_of_countable _) =
      i.midpointLaw K := by
  have hf : (RationalAffineAllocation.permutation i.permutation).real.value = permuteAllocation i.permutation :=
    funext (RationalAffineAllocation.permutation_real i.permutation)
  calc
    _ = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
        (fun scalarBits => (i.input.fixedIdealLaw K outerBits scalarBits).map
          (RationalAffineAllocation.permutation i.permutation).real.value) (measurable_of_countable _)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      intro outerBits
      apply averaged_fairBit_congr
      exact i.fixedIdealLaw_eq K outerBits
    _ = averagedLaw (fairBitLaw K) (fun outerBits => (averagedLaw (fairBitLaw K)
        (fun scalarBits => i.input.fixedIdealLaw K outerBits scalarBits) (measurable_of_countable _)).map
        (RationalAffineAllocation.permutation i.permutation).real.value) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      intro outerBits
      exact averaged_fairBit_affine K _ _
    _ = (averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
        (fun scalarBits => i.input.fixedIdealLaw K outerBits scalarBits) (measurable_of_countable _)) (measurable_of_countable _)).map
        (RationalAffineAllocation.permutation i.permutation).real.value :=
      averaged_fairBit_affine K _ _
    _ = _ := by
      rw [i.input.averaged_fixedIdeal K, hf]
      rfl

end Blotto.RationalFourSpec
