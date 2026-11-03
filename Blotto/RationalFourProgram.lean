import Blotto.RationalFourMachineLaw

/-! Actual bounded native four-variable sampling in both ordered cases.
One flat fair vector supplies the shared cap and both scalar blocks. -/

namespace Blotto.RationalFourInput
open MeasureTheory

def coinBitBudget (K : ℕ) : ℕ := 3 * (80 + K)
def innerBitBudget (K : ℕ) : ℕ := coinBitBudget K + K
def sampleBitBudget (K : ℕ) : ℕ := innerBitBudget K + K

theorem sampleBitBudget_eq (K : ℕ) : sampleBitBudget K = 5 * K + 240 := by
  unfold sampleBitBudget innerBitBudget coinBitBudget
  omega

def innerSample (i : RationalFourInput) (K : ℕ) (outerBits : Fin K → Bool)
    (innerBits : Fin (innerBitBudget K) → Bool) : Fin 4 → ℚ :=
  i.fixedSample K (coinBitBudget K) outerBits (secondBitBlock (coinBitBudget K) K innerBits)
    (firstBitBlock (coinBitBudget K) K innerBits)

def sample (i : RationalFourInput) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) : Fin 4 → ℚ :=
  i.innerSample K (secondBitBlock (innerBitBudget K) K bits) (firstBitBlock (innerBitBudget K) K bits)

noncomputable def innerLaw (i : RationalFourInput) (K : ℕ) (outerBits : Fin K → Bool) : Mixed 4 :=
  (fairBitLaw (innerBitBudget K)).map (fun bits j => (i.innerSample K outerBits bits j : ℝ))

noncomputable def sampleLaw (i : RationalFourInput) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (sampleBitBudget K)).map (fun bits j => (i.sample K bits j : ℝ))

theorem sample_fullBudget (i : RationalFourInput) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.sample K bits j : ℝ)) := i.fixedSample_fullBudget K _ _ _ _

theorem innerLaw_average (i : RationalFourInput) (K : ℕ) (outerBits : Fin K → Bool) :
    i.innerLaw K outerBits = averagedLaw (fairBitLaw K)
      (fun scalarBits => i.fixedLaw K (coinBitBudget K) outerBits scalarBits) (measurable_of_countable _) := by
  unfold innerLaw innerSample innerBitBudget
  convert! fairBitBlocks_law (n := 4) (coinBitBudget K) K
    (fun choiceBits scalarBits j => (i.fixedSample K (coinBitBudget K) outerBits scalarBits choiceBits j : ℝ)) using 1

theorem sampleLaw_average (i : RationalFourInput) (K : ℕ) :
    i.sampleLaw K = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => i.fixedLaw K (coinBitBudget K) outerBits scalarBits) (measurable_of_countable _)) (measurable_of_countable _) := by
  calc
    i.sampleLaw K = averagedLaw (fairBitLaw K) (i.innerLaw K) (measurable_of_countable _) := by
      unfold sampleLaw sample sampleBitBudget innerLaw
      convert! fairBitBlocks_law (n := 4) (innerBitBudget K) K
        (fun innerBits outerBits j => (i.innerSample K outerBits innerBits j : ℝ)) using 1
    _ = _ := by
      apply averaged_fairBit_congr
      exact i.innerLaw_average K

theorem sampleLaw_midpoint_CDF_error (i : RationalFourInput) (K : ℕ) :
    CDFClose (i.sampleLaw K) (i.midpointLaw K) (1 / (2 : ℝ) ^ K) := by
  rw [i.sampleLaw_average, ← i.averaged_fixedIdeal K]
  apply averaged_fairBit_CDFClose
  intro outerBits
  apply averaged_fairBit_CDFClose
  intro scalarBits
  exact i.fixedLaw_CDF_error K outerBits scalarBits

theorem sampleLaw_CDF_error (i : RationalFourInput) (K : ℕ) :
    CDFClose (i.sampleLaw K) i.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.sampleLaw_midpoint_CDF_error K).triangle (i.midpointLaw_CDF_error K)
  have hsum : 1 / (2 : ℝ) ^ K + 3 / (2 * (2 : ℝ) ^ K) = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

end Blotto.RationalFourInput
