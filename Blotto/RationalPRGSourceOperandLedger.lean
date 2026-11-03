import Blotto.RationalPRGWordExtractionPrice
import Blotto.RationalPRGClassificationPrice

/-! One ledger combines the source operand components on the exact paper
packet: initial data, prepared requests/words, stores and retention tests.
It excludes reader/address/control/Boolean-controller/local-coupling/backend
work. Resource copying remains an explicit price-model choice. -/

namespace Blotto.RationalPRGInput

def richSourceOperandBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richInitialDataBitCost model + i.richPaperSourceRequestBitCost model K bits +
    i.richPaperSourceStoreBitCost model copyResources K bits + i.richPaperSourceRetainedBitCost model K bits

def poorSourceOperandBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorInitialDataBitCost model + i.poorPaperSourceRequestBitCost model K bits +
    i.poorPaperSourceStoreBitCost model copyResources K bits + i.poorPaperSourceRetainedBitCost model K bits

theorem richSourceOperandBitCost_eq_initial {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSourceOperandBitCost model copyResources K bits = i.richInitialDataBitCost model := by
  rw [richSourceOperandBitCost, i.richPaperSourceRequestBitCost_eq_zero,
    i.richPaperSourceStoreBitCost_eq_zero, i.richPaperSourceRetainedBitCost_eq_zero]
  omega

theorem richSourceOperandBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSourceOperandBitCost model copyResources K bits ≤ 7 * n * model.rat (8 * i.inputWordWidth + 31) := by
  rw [i.richSourceOperandBitCost_eq_initial]
  have hWidth := model.monotone (by omega : 5 + 2 * i.inputWordWidth ≤ 8 * i.inputWordWidth + 31)
  exact (i.richInitialDataBitCost_bound model).trans (Nat.mul_le_mul_left (7 * n) hWidth)

theorem poorSourceOperandBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSourceOperandBitCost model copyResources K bits ≤
      (105 * n + ((if copyResources then 2 * n + 30 else 32) + 10) * (n - 1)) * model.rat (8 * i.inputWordWidth + 31) := by
  have hWidth := model.monotone (by omega : 5 + 2 * i.inputWordWidth ≤ 8 * i.inputWordWidth + 31)
  have hInitial := (i.poorInitialDataBitCost_bound model).trans (Nat.mul_le_mul_left (7 * n) hWidth)
  have hRequest := (i.poorPaperSourceRequestBitCost_bound model K bits).trans (Nat.mul_le_mul_left (98 * n) hWidth)
  have hStore := i.poorPaperSourceStoreBitCost_bound model copyResources K bits
  have hRetained := (i.poorPaperSourceRetainedBitCost_bound model K bits).trans (Nat.mul_le_mul_left (10 * (n - 1)) hWidth)
  calc
    _ ≤ 7 * n * model.rat (8 * i.inputWordWidth + 31) + 98 * n * model.rat (8 * i.inputWordWidth + 31) +
        (if copyResources then 2 * n + 30 else 32) * (n - 1) * model.rat (8 * i.inputWordWidth + 31) +
        10 * (n - 1) * model.rat (8 * i.inputWordWidth + 31) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hInitial hRequest) hStore) hRetained
    _ = _ := by ring

theorem poorSourceOperandBitCost_logical_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSourceOperandBitCost model false K bits ≤ 147 * n * model.rat (8 * i.inputWordWidth + 31) := by
  have h := i.poorSourceOperandBitCost_bound model false K bits
  have hCoeff : 105 * n + (32 + 10) * (n - 1) ≤ 147 * n := by omega
  exact h.trans (Nat.mul_le_mul_right _ hCoeff)

theorem poorSourceOperandBitCost_fullCopy_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSourceOperandBitCost model true K bits ≤ (2 * n * n + 143 * n) * model.rat (8 * i.inputWordWidth + 31) := by
  have h := i.poorSourceOperandBitCost_bound model true K bits
  have hCoeff : 105 * n + (2 * n + 30 + 10) * (n - 1) ≤ 2 * n * n + 143 * n := by
    have hn : n - 1 ≤ n := Nat.sub_le _ _
    have hn1 : n = 0 ∨ n - 1 + 1 = n := by omega
    rcases hn1 with hn0 | hnPos
    · subst n; omega
    · nlinarith
  exact h.trans (Nat.mul_le_mul_right _ hCoeff)

end Blotto.RationalPRGInput
