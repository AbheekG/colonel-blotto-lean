import Blotto.RationalNestedSpecLaw

/-! The full positive-length nested sampler: q=0/1 and either coordinate
order use the same bounded native rational interface and every-path budget. -/

namespace Blotto.RationalNestedSpec
open MeasureTheory

def conditionalSample (i : RationalNestedSpec) (K : ℕ)
    (innerBits : Fin (RationalNestedInput.conditionalBitBudget K) → Bool)
    (outerBits : Fin K → Bool) : Fin 3 → ℚ :=
  (i.profile K outerBits).flatSample 0 (3 * (17 + K)) K innerBits

def sample (i : RationalNestedSpec) (K : ℕ)
    (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) : Fin 3 → ℚ :=
  i.conditionalSample K (firstBitBlock (RationalNestedInput.conditionalBitBudget K) K bits)
    (secondBitBlock (RationalNestedInput.conditionalBitBudget K) K bits)

noncomputable def sampleLaw (i : RationalNestedSpec) (K : ℕ) : Mixed 3 :=
  (fairBitLaw (RationalNestedInput.sampleBitBudget K)).map (fun bits j => (i.sample K bits j : ℝ))

theorem sample_fullBudget (i : RationalNestedSpec) (K : ℕ)
    (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) :
    FullBudget (i.M : ℝ) (fun j => (i.sample K bits j : ℝ)) := by
  apply RationalSegmentLottery.flatSample_fullBudget
  exact i.profile_endpoints K _

theorem sampleLaw_average (i : RationalNestedSpec) (K : ℕ) :
    i.sampleLaw K = averagedLaw (fairBitLaw K)
      (fun outerBits => (i.profile K outerBits).flatLaw 0 (3 * (17 + K)) K) (measurable_of_countable _) := by
  calc
    i.sampleLaw K = averagedLaw (fairBitLaw K) (fun outerBits =>
      (fairBitLaw (RationalNestedInput.conditionalBitBudget K)).map
        (fun innerBits j => (i.conditionalSample K innerBits outerBits j : ℝ)))
      (measurable_of_countable _) := by
        unfold sampleLaw RationalNestedInput.sampleBitBudget sample
        convert! fairBitBlocks_law (n := 3) (RationalNestedInput.conditionalBitBudget K) K
          (fun innerBits outerBits j => (i.conditionalSample K innerBits outerBits j : ℝ)) using 1
    _ = _ := rfl

theorem sampleLaw_location_error (i : RationalNestedSpec) (K : ℕ) :
    CDFClose (i.sampleLaw K) (i.locationLaw K) (3 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.sampleLaw_average]
  unfold locationLaw
  rw [averaged_fairBit_finite, averaged_fairBit_finite]
  apply probabilityMixture_CDFClose
  intro scalarIndex
  exact (i.profile K ((bitIndexEquiv K).symm scalarIndex)).flatLaw_CDF_error 0 K

theorem sampleLaw_CDF_error (i : RationalNestedSpec) (K : ℕ) :
    CDFClose (i.sampleLaw K) i.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.sampleLaw_location_error K).triangle (i.locationLaw_CDF_error K)
  have hsum : 3 / (2 * (2 : ℝ) ^ K) + 1 / (2 : ℝ) ^ K = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

end Blotto.RationalNestedSpec
