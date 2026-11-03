import Blotto.RationalFirstConditional
import Blotto.RationalThreeProgram
import Blotto.FirstDyadicApproximation

/-! The first nested case has a fully native rational bounded sampler. A
fresh midpoint location determines its conditional table; all component
choices and interpolation are then executed with the remaining blocks. -/

namespace Blotto.RationalNestedInput
open MeasureTheory
open scoped BigOperators

def midpointLocation (i : RationalNestedInput) (K : ℕ) (bits : Fin K → Bool) : ℚ :=
  i.location (dyadicMidpointSample K bits)

theorem midpointLocation_bounds (i : RationalNestedInput) (K : ℕ) (bits : Fin K → Bool) :
    0 ≤ i.midpointLocation K bits ∧ i.midpointLocation K bits ≤ i.t := by
  apply i.location_bounds
  constructor
  · exact_mod_cast le_of_lt (dyadicMidpointSample_bounds K bits).1
  · exact_mod_cast le_of_lt (dyadicMidpointSample_bounds K bits).2

theorem midpointLocation_real (i : RationalNestedInput) (K : ℕ) (bits : Fin K → Bool) :
    (i.midpointLocation K bits : ℝ) = i.real.location (dyadicMidpointSample K bits) := i.location_real _

def firstConditionalSample (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ)
    (innerBits : Fin (RationalThreeSpec.sampleBitBudget K) → Bool) (outerBits : Fin K → Bool) : Fin 3 → ℚ :=
  (i.firstConditionalLottery htv (i.midpointLocation K outerBits) (i.midpointLocation_bounds K outerBits)).flatSample
    0 (3 * (8 + K)) K innerBits

def firstSampleBitBudget (K : ℕ) : ℕ := RationalThreeSpec.sampleBitBudget K + K

theorem firstSampleBitBudget_eq (K : ℕ) : firstSampleBitBudget K = 5 * K + 24 := by
  unfold firstSampleBitBudget
  rw [RationalThreeSpec.sampleBitBudget_eq]
  omega

def firstSample (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ)
    (bits : Fin (firstSampleBitBudget K) → Bool) : Fin 3 → ℚ :=
  i.firstConditionalSample htv K (firstBitBlock (RationalThreeSpec.sampleBitBudget K) K bits)
    (secondBitBlock (RationalThreeSpec.sampleBitBudget K) K bits)

noncomputable def firstSampleLaw (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ) : Mixed 3 :=
  (fairBitLaw (firstSampleBitBudget K)).map (fun bits j => (i.firstSample htv K bits j : ℝ))

theorem firstSample_fullBudget (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ)
    (bits : Fin (firstSampleBitBudget K) → Bool) :
    FullBudget (i.M : ℝ) (fun j => (i.firstSample htv K bits j : ℝ)) := by
  apply RationalSegmentLottery.flatSample_fullBudget
  intro slot
  exact i.firstConditionalLottery_endpoints htv _ _ slot

theorem firstSampleLaw_average (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    i.firstSampleLaw htv K = averagedLaw (fairBitLaw K)
      (fun outerBits => (i.firstConditionalLottery htv (i.midpointLocation K outerBits)
        (i.midpointLocation_bounds K outerBits)).flatLaw 0 (3 * (8 + K)) K)
      (measurable_of_countable _) := by
  calc
    i.firstSampleLaw htv K = averagedLaw (fairBitLaw K)
      (fun outerBits => (fairBitLaw (RationalThreeSpec.sampleBitBudget K)).map
        (fun innerBits j => (i.firstConditionalSample htv K innerBits outerBits j : ℝ)))
      (measurable_of_countable _) := by
        unfold firstSampleLaw firstSampleBitBudget firstSample
        convert! fairBitBlocks_law (n := 3) (RationalThreeSpec.sampleBitBudget K) K
          (fun innerBits outerBits j => (i.firstConditionalSample htv K innerBits outerBits j : ℝ)) using 1
    _ = _ := rfl

theorem firstSampleLaw_location_error (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    CDFClose (i.firstSampleLaw htv K) (i.real.firstLocationApproximation (i.firstCase_real htv) K)
      (3 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.firstSampleLaw_average, averaged_fairBit_finite,
    i.real.firstLocationApproximation_eq_mixture (i.firstCase_real htv) K]
  apply probabilityMixture_CDFClose
  intro scalarIndex
  have he := i.firstConditionalLottery_flatLaw_CDF_error htv
    (i.midpointLocation K ((bitIndexEquiv K).symm scalarIndex))
    (i.midpointLocation_bounds K ((bitIndexEquiv K).symm scalarIndex)) K
  have hs : (i.midpointLocation K ((bitIndexEquiv K).symm scalarIndex) : ℝ) =
      i.real.location (midpoint scalarIndex) := by
    rw [i.midpointLocation_real, dyadicMidpointSample_real]
    change i.real.location (midpoint ((bitIndexEquiv K) ((bitIndexEquiv K).symm scalarIndex))) = _
    rw [Equiv.apply_symm_apply]
  rw [hs] at he
  exact he

theorem firstSampleLaw_CDF_error (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    CDFClose (i.firstSampleLaw htv K) (i.real.firstLaw (i.firstCase_real htv))
      (5 / (2 * (2 : ℝ) ^ K)) := by
  have he := (i.firstSampleLaw_location_error htv K).triangle
    (i.real.firstLocationApproximation_CDF_error (i.firstCase_real htv) K)
  have hsum : 3 / (2 * (2 : ℝ) ^ K) + 1 / (2 : ℝ) ^ K = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at he
  exact he

end Blotto.RationalNestedInput
