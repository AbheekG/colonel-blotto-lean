import Blotto.RationalPRGReaderWork
import Blotto.RationalPRGSourceControllerWork

/-! Source operand and derived-input prices, then source Boolean/encoding
labels, compose on the same paper packet. Original input addressing, other
control/local-coupling/output and physical ownership/backend remain separate. -/

namespace Blotto.RationalPRGInput

def richSourceDataAndReaderCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richSourceOperandBitCost model copyResources K bits + i.richReaderTotal model K bits

def poorSourceDataAndReaderCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorSourceOperandBitCost model copyResources K bits + i.poorReaderTotal model K bits

theorem richSourceDataAndReaderCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSourceDataAndReaderCost model copyResources K bits ≤ 15 * n * model.rat (8 * i.inputWordWidth + 31) := by
  have hOperands := i.richSourceOperandBitCost_bound model copyResources K bits
  have hWidth := model.monotone (by omega : 5 + 2 * i.inputWordWidth ≤ 8 * i.inputWordWidth + 31)
  have hReaders := (i.richReaderTotal_bound model K bits).trans (Nat.mul_le_mul_left (8 * n) hWidth)
  unfold richSourceDataAndReaderCost
  nlinarith

theorem poorSourceDataAndReaderCost_logical_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSourceDataAndReaderCost model false K bits ≤ 175 * n * model.rat (8 * i.inputWordWidth + 31) := by
  have hOperands := i.poorSourceOperandBitCost_logical_bound model K bits
  have hWidth := model.monotone (by omega : 5 + 2 * i.inputWordWidth ≤ 8 * i.inputWordWidth + 31)
  have hReaders := (i.poorReaderTotal_bound model K bits).trans (Nat.mul_le_mul_left (28 * n) hWidth)
  unfold poorSourceDataAndReaderCost
  nlinarith

theorem poorSourceDataAndReaderCost_fullCopy_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSourceDataAndReaderCost model true K bits ≤ (2 * n * n + 171 * n) * model.rat (8 * i.inputWordWidth + 31) := by
  have hOperands := i.poorSourceOperandBitCost_fullCopy_bound model K bits
  have hWidth := model.monotone (by omega : 5 + 2 * i.inputWordWidth ≤ 8 * i.inputWordWidth + 31)
  have hReaders := (i.poorReaderTotal_bound model K bits).trans (Nat.mul_le_mul_left (28 * n) hWidth)
  unfold poorSourceDataAndReaderCost
  nlinarith

def richSourceProcessingAllowance {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richSourceDataAndReaderCost model copyResources K bits + i.richPaperSourceControllerWork K bits

def poorSourceProcessingAllowance {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorSourceDataAndReaderCost model copyResources K bits + i.poorPaperSourceControllerWork K bits

theorem richSourceProcessingAllowance_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSourceProcessingAllowance model copyResources K bits ≤ 15 * n * model.rat (8 * i.inputWordWidth + 31) +
      (24 * i.inputWordWidth + 52) * (9 * n + 6 * K + 6242) := by
  have hData := i.richSourceDataAndReaderCost_bound model copyResources K bits
  have hController := (i.richPaperSourceControllerWork_bound K bits).trans (sourceControllerAllowance_linear n K i.inputWordWidth)
  exact Nat.add_le_add hData hController

theorem poorSourceProcessingAllowance_logical_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSourceProcessingAllowance model false K bits ≤ 175 * n * model.rat (8 * i.inputWordWidth + 31) +
      (24 * i.inputWordWidth + 52) * (9 * n + 6 * K + 6242) := by
  have hData := i.poorSourceDataAndReaderCost_logical_bound model K bits
  have hController := (i.poorPaperSourceControllerWork_bound K bits).trans (sourceControllerAllowance_linear n K i.inputWordWidth)
  exact Nat.add_le_add hData hController

end Blotto.RationalPRGInput
