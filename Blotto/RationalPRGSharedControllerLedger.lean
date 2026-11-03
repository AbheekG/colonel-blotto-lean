import Blotto.RationalLottoSharedControllerWork
import Blotto.RationalPRGSharedSourceLedger

/-! The primary paper packets carry source encoding/coin work along with
source operands and derived-input costs. Rich source coin work is exactly zero.
These remain components of the full algorithm, with backend/ownership separate. -/

namespace Blotto.RationalLottoResourceSystem

def sharedPaperSourceControllerWork {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedSourceControllerWork (coinBitBudget n K) (firstBitBlock (coinBitBudget n K) K inner)

theorem sharedPaperSourceControllerWork_refines {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) :
    i.sharedPaperSourceControllerWork K bits = i.paperSourceControllerWork K bits :=
  i.sharedSourceControllerWork_refines K _ _ _ _

theorem sharedPaperSourceControllerWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.sharedPaperSourceControllerWork K bits ≤ 4 * binaryWordWidth D * (n - 1) +
      (24 * binaryWordWidth D + 28) * (2 * (n - 1) + 2 * coinBitBudget n K + 2) :=
  i.sharedSourceControllerWork_bound D hD hB hL hR _ _

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

def sharedSourceControllerAllowance (n K inputWidth : ℕ) : ℕ :=
  4 * (1 + inputWidth) * (n - 1) +
    (24 * (1 + inputWidth) + 28) * (2 * (n - 1) + 2 * RationalLottoResourceSystem.coinBitBudget n K + 2)

theorem sharedSourceControllerAllowance_linear (n K inputWidth : ℕ) :
    sharedSourceControllerAllowance n K inputWidth ≤ (24 * inputWidth + 52) * (9 * n + 6 * K + 6002) := by
  have hn : n - 1 ≤ n := Nat.sub_le _ _
  unfold sharedSourceControllerAllowance RationalLottoResourceSystem.coinBitBudget
  nlinarith

theorem richSharedPaperSourceControllerWork_eq_zero {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.sharedPaperSourceControllerWork K bits = 0 :=
  i.richNativeSystem.sharedSourceControllerWork_zero_rank _ _ i.richResource_rank_zero

theorem poorSharedPaperSourceControllerWork_bound {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorNativeSystem.sharedPaperSourceControllerWork K bits ≤ sharedSourceControllerAllowance n K i.inputWordWidth := by
  have h := i.poorNativeSystem.sharedPaperSourceControllerWork_bound i.latticeDenominator i.latticeDenominator_pos
    i.b_le i.lengths_on_lattice i.poorInitial_on_lattice K bits
  have hw := i.latticeDenominator_wordWidth
  have hEncoding := Nat.mul_le_mul_right (n - 1) (Nat.mul_le_mul_left 4 hw)
  have hRate : 24 * binaryWordWidth i.latticeDenominator + 28 ≤ 24 * (1 + i.inputWordWidth) + 28 := by omega
  have hBody := Nat.mul_le_mul_right
    (2 * (n - 1) + 2 * RationalLottoResourceSystem.coinBitBudget n K + 2) hRate
  exact h.trans (Nat.add_le_add hEncoding hBody)

def richSharedSourceProcessingAllowance {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richSharedSourceDataAndReaderCost model copyResources K bits + i.richNativeSystem.sharedPaperSourceControllerWork K bits

def poorSharedSourceProcessingAllowance {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorSharedSourceDataAndReaderCost model copyResources K bits + i.poorNativeSystem.sharedPaperSourceControllerWork K bits

theorem richSharedSourceProcessingAllowance_refines {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSharedSourceProcessingAllowance model copyResources K bits = i.richSourceProcessingAllowance model copyResources K bits := by
  rw [richSharedSourceProcessingAllowance, i.richSharedSourceDataAndReaderCost_refines,
    RationalLottoResourceSystem.sharedPaperSourceControllerWork_refines]
  rfl

theorem poorSharedSourceProcessingAllowance_refines {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedSourceProcessingAllowance model copyResources K bits = i.poorSourceProcessingAllowance model copyResources K bits := by
  rw [poorSharedSourceProcessingAllowance, i.poorSharedSourceDataAndReaderCost_refines,
    RationalLottoResourceSystem.sharedPaperSourceControllerWork_refines]
  rfl

theorem richSharedSourceProcessingAllowance_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSharedSourceProcessingAllowance model copyResources K bits ≤ 15 * n * model.rat (8 * i.inputWordWidth + 31) := by
  rw [richSharedSourceProcessingAllowance, i.richSharedPaperSourceControllerWork_eq_zero, Nat.add_zero]
  exact i.richSharedSourceDataAndReaderCost_bound model copyResources K bits

theorem poorSharedSourceProcessingAllowance_logical_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedSourceProcessingAllowance model false K bits ≤ 175 * n * model.rat (8 * i.inputWordWidth + 31) +
      (24 * i.inputWordWidth + 52) * (9 * n + 6 * K + 6002) := by
  have hData := i.poorSharedSourceDataAndReaderCost_logical_bound model K bits
  have hControl := (i.poorSharedPaperSourceControllerWork_bound K bits).trans (sharedSourceControllerAllowance_linear n K i.inputWordWidth)
  exact Nat.add_le_add hData hControl

theorem poorSharedSourceProcessingAllowance_fullCopy_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedSourceProcessingAllowance model true K bits ≤ (2 * n * n + 171 * n) * model.rat (8 * i.inputWordWidth + 31) +
      (24 * i.inputWordWidth + 52) * (9 * n + 6 * K + 6002) := by
  have hData := i.poorSharedSourceDataAndReaderCost_fullCopy_bound model K bits
  have hControl := (i.poorSharedPaperSourceControllerWork_bound K bits).trans (sharedSourceControllerAllowance_linear n K i.inputWordWidth)
  exact Nat.add_le_add hData hControl

end Blotto.RationalPRGInput
