import Blotto.RationalFourSmallMachineLaw

/-! Complete bounded native sampler for the four-variable atom-conditioning
branch. One fair vector supplies R=3(20+K) shared coin bits and two fresh K-bit
scalar blocks; every returned path, including fallback, is budget/box feasible. -/

namespace Blotto.RationalFourInput
open MeasureTheory

def smallCoinBitBudget (K : ℕ) : ℕ := 3 * (20 + K)
def smallInnerBitBudget (K : ℕ) : ℕ := smallCoinBitBudget K + K
def smallSampleBitBudget (K : ℕ) : ℕ := smallInnerBitBudget K + K

theorem smallSampleBitBudget_eq (K : ℕ) : smallSampleBitBudget K = 5 * K + 60 := by
  unfold smallSampleBitBudget smallInnerBitBudget smallCoinBitBudget
  omega

def smallInnerSample (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits : Fin K → Bool) (innerBits : Fin (smallInnerBitBudget K) → Bool) : Fin 4 → ℚ :=
  i.smallFixedSample hcase K (smallCoinBitBudget K) outerBits (secondBitBlock (smallCoinBitBudget K) K innerBits)
    (firstBitBlock (smallCoinBitBudget K) K innerBits)

def smallSample (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (bits : Fin (smallSampleBitBudget K) → Bool) : Fin 4 → ℚ :=
  i.smallInnerSample hcase K (secondBitBlock (smallInnerBitBudget K) K bits) (firstBitBlock (smallInnerBitBudget K) K bits)

noncomputable def smallInnerLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits : Fin K → Bool) : Mixed 4 :=
  (fairBitLaw (smallInnerBitBudget K)).map (fun bits j => (i.smallInnerSample hcase K outerBits bits j : ℝ))

noncomputable def smallSampleLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (smallSampleBitBudget K)).map (fun bits j => (i.smallSample hcase K bits j : ℝ))

theorem smallSample_contract (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (bits : Fin (smallSampleBitBudget K) → Bool) : i.SmallPathContract (i.smallSample hcase K bits) :=
  i.smallFixedSample_contract hcase K _ _ _ _

theorem smallInnerLaw_average (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits : Fin K → Bool) :
    i.smallInnerLaw hcase K outerBits = averagedLaw (fairBitLaw K)
      (fun scalarBits => i.smallFixedLaw hcase K (smallCoinBitBudget K) outerBits scalarBits) (measurable_of_countable _) := by
  unfold smallInnerLaw smallInnerSample smallInnerBitBudget
  convert! fairBitBlocks_law (n := 4) (smallCoinBitBudget K) K
    (fun choiceBits scalarBits j => (i.smallFixedSample hcase K (smallCoinBitBudget K) outerBits scalarBits choiceBits j : ℝ)) using 1

theorem smallSampleLaw_average (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    i.smallSampleLaw hcase K = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => i.smallFixedLaw hcase K (smallCoinBitBudget K) outerBits scalarBits) (measurable_of_countable _))
      (measurable_of_countable _) := by
  calc
    i.smallSampleLaw hcase K = averagedLaw (fairBitLaw K) (i.smallInnerLaw hcase K) (measurable_of_countable _) := by
      unfold smallSampleLaw smallSample smallSampleBitBudget smallInnerLaw
      convert! fairBitBlocks_law (n := 4) (smallInnerBitBudget K) K
        (fun innerBits outerBits j => (i.smallInnerSample hcase K outerBits innerBits j : ℝ)) using 1
    _ = _ := by
      apply averaged_fairBit_congr
      exact i.smallInnerLaw_average hcase K

theorem smallSampleLaw_midpoint_CDF_error (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.smallSampleLaw hcase K) (i.smallMidpointLaw hcase K) (1 / (2 : ℝ) ^ K) := by
  rw [i.smallSampleLaw_average, ← i.averaged_smallFixedIdeal hcase K]
  apply averaged_fairBit_CDFClose
  intro outerBits
  apply averaged_fairBit_CDFClose
  intro scalarBits
  exact i.smallFixedLaw_CDF_error hcase K outerBits scalarBits

theorem smallSampleLaw_CDF_error (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    CDFClose (i.smallSampleLaw hcase K) (i.real.smallCaseLaw (i.smallCase_real hcase)) (5 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.smallSampleLaw_midpoint_CDF_error hcase K).triangle (i.smallMidpointLaw_CDF_error hcase K)
  have hsum : 1 / (2 : ℝ) ^ K + 3 / (2 * (2 : ℝ) ^ K) = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

end Blotto.RationalFourInput
