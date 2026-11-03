import Blotto.RationalNestedResourceMachineLaw
import Blotto.AveragedBitCDF
import Blotto.FairBitBlocks

/-! The native three-resource/nested sampler uses one flat fair vector:
R=3(19+K) adaptive coin bits, K segment bits and K location bits. Its actual
whole law is linked to the ideal midpoint law, with one cap contribution. -/

namespace Blotto.RationalNestedResourceSystem
open MeasureTheory

def coinBitBudget (K : ℕ) : ℕ := 3 * (19 + K)
def innerBitBudget (K : ℕ) : ℕ := coinBitBudget K + K
def sampleBitBudget (K : ℕ) : ℕ := innerBitBudget K + K

theorem sampleBitBudget_eq (K : ℕ) : sampleBitBudget K = 5 * K + 57 := by
  unfold sampleBitBudget innerBitBudget coinBitBudget
  omega

def innerSample (i : RationalNestedResourceSystem) (K : ℕ) (outerBits : Fin K → Bool)
    (innerBits : Fin (innerBitBudget K) → Bool) : Fin 3 → ℚ :=
  i.fixedSample K (coinBitBudget K) outerBits (secondBitBlock (coinBitBudget K) K innerBits)
    (firstBitBlock (coinBitBudget K) K innerBits)

def sample (i : RationalNestedResourceSystem) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) : Fin 3 → ℚ :=
  i.innerSample K (secondBitBlock (innerBitBudget K) K bits) (firstBitBlock (innerBitBudget K) K bits)

noncomputable def innerLaw (i : RationalNestedResourceSystem) (K : ℕ) (outerBits : Fin K → Bool) : Mixed 3 :=
  (fairBitLaw (innerBitBudget K)).map (fun bits j => (i.innerSample K outerBits bits j : ℝ))

noncomputable def sampleLaw (i : RationalNestedResourceSystem) (K : ℕ) : Mixed 3 :=
  (fairBitLaw (sampleBitBudget K)).map (fun bits j => (i.sample K bits j : ℝ))

theorem sample_contract (i : RationalNestedResourceSystem) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) :
    i.PathContract (i.sample K bits) := i.fixedSample_contract K _ _ _ _

theorem innerLaw_average (i : RationalNestedResourceSystem) (K : ℕ) (outerBits : Fin K → Bool) :
    i.innerLaw K outerBits = averagedLaw (fairBitLaw K)
      (fun scalarBits => i.fixedLaw K (coinBitBudget K) outerBits scalarBits) (measurable_of_countable _) := by
  unfold innerLaw innerSample innerBitBudget
  convert! fairBitBlocks_law (n := 3) (coinBitBudget K) K
    (fun choiceBits scalarBits j => (i.fixedSample K (coinBitBudget K) outerBits scalarBits choiceBits j : ℝ)) using 1

theorem sampleLaw_average (i : RationalNestedResourceSystem) (K : ℕ) :
    i.sampleLaw K = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => i.fixedLaw K (coinBitBudget K) outerBits scalarBits) (measurable_of_countable _)) (measurable_of_countable _) := by
  calc
    i.sampleLaw K = averagedLaw (fairBitLaw K) (i.innerLaw K) (measurable_of_countable _) := by
      unfold sampleLaw sample sampleBitBudget innerLaw
      convert! fairBitBlocks_law (n := 3) (innerBitBudget K) K
        (fun innerBits outerBits j => (i.innerSample K outerBits innerBits j : ℝ)) using 1
    _ = _ := by
      apply averaged_fairBit_congr
      exact i.innerLaw_average K

theorem sampleLaw_midpoint_CDF_error (i : RationalNestedResourceSystem) (K : ℕ) :
    CDFClose (i.sampleLaw K) (i.midpointLaw K) (1 / (2 : ℝ) ^ K) := by
  rw [i.sampleLaw_average, ← i.averaged_fixedIdeal K]
  apply averaged_fairBit_CDFClose
  intro outerBits
  apply averaged_fairBit_CDFClose
  intro scalarBits
  exact i.fixedLaw_CDF_error K outerBits scalarBits

theorem sampleLaw_CDF_error (i : RationalNestedResourceSystem) (K : ℕ) :
    CDFClose (i.sampleLaw K) i.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.sampleLaw_midpoint_CDF_error K).triangle (i.midpointLaw_CDF_error K)
  have hsum : 1 / (2 : ℝ) ^ K + 3 / (2 * (2 : ℝ) ^ K) = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

end Blotto.RationalNestedResourceSystem
