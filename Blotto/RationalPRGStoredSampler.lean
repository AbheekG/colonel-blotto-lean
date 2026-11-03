import Blotto.RationalStoredPaperSampler
import Blotto.RationalPRGOriginalSampler

/-! Original-budget PRG producers draw one complete stored row and then map
scaling over its data. Their whole fair-bit laws equal the existing laws. -/

namespace Blotto

def RationalResourceArray.scaled {n : ℕ} (a : ℚ) (row : RationalResourceArray n) : RationalResourceArray n :=
  ⟨row.data.map (fun q => a * q), by simp only [Array.size_map, row.size]⟩

theorem RationalResourceArray.scaled_allocation {n : ℕ} (a : ℚ) (row : RationalResourceArray n) :
    (row.scaled a).allocation = fun j => a * row.allocation j := by
  funext j
  simp only [scaled, allocation, Array.getElem_map]

namespace RationalPRGOriginalInput
open MeasureTheory

def storedRichSample {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : RationalResourceArray n :=
  let normalized := i.normalizedInput
  let row := normalized.richNativeSystem.storedPaperSample K bits
  row.scaled i.a

def storedPoorSample {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : RationalResourceArray n :=
  let normalized := i.normalizedInput
  let row := normalized.poorNativeSystem.storedPaperSample K bits
  row.scaled i.a

theorem storedRichSample_allocation {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (i.storedRichSample K bits).allocation = i.richSample K bits := by
  unfold storedRichSample
  rw [RationalResourceArray.scaled_allocation, RationalLottoResourceSystem.storedPaperSample_allocation]
  funext j
  exact (i.richSample_apply K bits j).symm

theorem storedPoorSample_allocation {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (i.storedPoorSample K bits).allocation = i.poorSample K bits := by
  unfold storedPoorSample
  rw [RationalResourceArray.scaled_allocation, RationalLottoResourceSystem.storedPaperSample_allocation]
  funext j
  exact (i.poorSample_apply K bits j).symm

theorem storedRichSample_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (i.a : ℝ) (i.storedRichSample K bits).realAllocation := by
  change FullBudget (i.a : ℝ) (fun j => ((i.storedRichSample K bits).allocation j : ℝ))
  rw [i.storedRichSample_allocation]
  exact i.richSample_fullBudget K bits

theorem storedPoorSample_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (i.b : ℝ) (i.storedPoorSample K bits).realAllocation := by
  change FullBudget (i.b : ℝ) (fun j => ((i.storedPoorSample K bits).allocation j : ℝ))
  rw [i.storedPoorSample_allocation]
  exact i.poorSample_fullBudget K bits

noncomputable def storedRichLaw {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map
    (fun bits => (i.storedRichSample K bits).realAllocation)

noncomputable def storedPoorLaw {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map
    (fun bits => (i.storedPoorSample K bits).realAllocation)

theorem storedRichLaw_eq {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    i.storedRichLaw K = i.richSampleLaw K := by
  unfold storedRichLaw richSampleLaw RationalResourceArray.realAllocation
  simp only [i.storedRichSample_allocation]

theorem storedPoorLaw_eq {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    i.storedPoorLaw K = i.poorSampleLaw K := by
  unfold storedPoorLaw poorSampleLaw RationalResourceArray.realAllocation
  simp only [i.storedPoorSample_allocation]

theorem storedSample_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    regret i.realValues (i.a : ℝ) (i.storedRichLaw K) (i.storedPoorLaw K) ≤ 5 / (2 : ℝ) ^ K ∧
      regret i.realValues (i.b : ℝ) (i.storedPoorLaw K) (i.storedRichLaw K) ≤ 5 / (2 : ℝ) ^ K := by
  rw [i.storedRichLaw_eq, i.storedPoorLaw_eq]
  exact i.sample_regrets K

theorem storedAccuracy_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (ε : ℚ) (hε : 0 < ε) :
    regret i.realValues (i.a : ℝ) (i.storedRichLaw (rationalAccuracyPrecision ε))
      (i.storedPoorLaw (rationalAccuracyPrecision ε)) < (ε : ℝ) ∧
      regret i.realValues (i.b : ℝ) (i.storedPoorLaw (rationalAccuracyPrecision ε))
        (i.storedRichLaw (rationalAccuracyPrecision ε)) < (ε : ℝ) := by
  rw [i.storedRichLaw_eq, i.storedPoorLaw_eq]
  exact i.rational_accuracy_regrets ε hε

end RationalPRGOriginalInput
end Blotto
