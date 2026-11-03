import Blotto.RationalNestedProfileLaw

/-! A native bounded sampler for all ordered interior nested cases. The
location block determines one 18-slot descriptor; its component choices share
one cap, and a fresh midpoint block interpolates the selected segment. -/

namespace Blotto.RationalNestedInput
open MeasureTheory

def conditionalBitBudget (K : ℕ) : ℕ := 3 * (17 + K) + K
def sampleBitBudget (K : ℕ) : ℕ := conditionalBitBudget K + K

theorem sampleBitBudget_eq (K : ℕ) : sampleBitBudget K = 5 * K + 51 := by
  unfold sampleBitBudget conditionalBitBudget
  omega

def conditionalSample (i : RationalNestedInput) (K : ℕ)
    (innerBits : Fin (conditionalBitBudget K) → Bool) (outerBits : Fin K → Bool) : Fin 3 → ℚ :=
  (i.profile K outerBits).flatSample 0 (3 * (17 + K)) K innerBits

def sample (i : RationalNestedInput) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) : Fin 3 → ℚ :=
  i.conditionalSample K (firstBitBlock (conditionalBitBudget K) K bits)
    (secondBitBlock (conditionalBitBudget K) K bits)

noncomputable def sampleLaw (i : RationalNestedInput) (K : ℕ) : Mixed 3 :=
  (fairBitLaw (sampleBitBudget K)).map (fun bits j => (i.sample K bits j : ℝ))

theorem sample_fullBudget (i : RationalNestedInput) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) :
    FullBudget (i.M : ℝ) (fun j => (i.sample K bits j : ℝ)) := by
  apply RationalSegmentLottery.flatSample_fullBudget
  exact i.profile_endpoints K _

theorem sampleLaw_average (i : RationalNestedInput) (K : ℕ) :
    i.sampleLaw K = averagedLaw (fairBitLaw K)
      (fun outerBits => (i.profile K outerBits).flatLaw 0 (3 * (17 + K)) K) (measurable_of_countable _) := by
  calc
    i.sampleLaw K = averagedLaw (fairBitLaw K) (fun outerBits =>
      (fairBitLaw (conditionalBitBudget K)).map (fun innerBits j => (i.conditionalSample K innerBits outerBits j : ℝ)))
      (measurable_of_countable _) := by
        unfold sampleLaw sampleBitBudget sample
        convert! fairBitBlocks_law (n := 3) (conditionalBitBudget K) K
          (fun innerBits outerBits j => (i.conditionalSample K innerBits outerBits j : ℝ)) using 1
    _ = _ := rfl

theorem sampleLaw_location_error (i : RationalNestedInput) (K : ℕ) :
    CDFClose (i.sampleLaw K) (i.locationLaw K) (3 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.sampleLaw_average]
  unfold locationLaw
  rw [averaged_fairBit_finite, averaged_fairBit_finite]
  apply probabilityMixture_CDFClose
  intro scalarIndex
  exact (i.profile K ((bitIndexEquiv K).symm scalarIndex)).flatLaw_CDF_error 0 K

theorem sampleLaw_CDF_error (i : RationalNestedInput) (K : ℕ) :
    CDFClose (i.sampleLaw K) i.real.couplingLaw (5 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.sampleLaw_location_error K).triangle (i.locationLaw_CDF_error K)
  have hsum : 3 / (2 * (2 : ℝ) ^ K) + 1 / (2 : ℝ) ^ K = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

end Blotto.RationalNestedInput
