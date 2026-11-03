import Blotto.RationalLottoSharedTerminalWork
import Blotto.RationalPRGSharedControllerLedger

/-! The same primary paper packet pays for source processing and one-time
terminal packing/routing. These are components, not a complete PRG time bound:
local coupling, output, backend, address/list/control and ownership are separate. -/

namespace Blotto.RationalLottoResourceSystem

def sharedPaperTerminalPreparationWork {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedTerminalPreparationWork model K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem sharedPaperTerminalPreparationWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.sharedPaperTerminalPreparationWork model K bits ≤ (17 * n + 15) * model.rat (i.terminalCacheWidth D) :=
  i.sharedTerminalPreparationWork_bound model D hD hB hL K _ _ _ _

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

def sourceAndPackingWidth {n : ℕ} (i : RationalPRGInput n) : ℕ :=
  max (binaryWordWidth (n + 4)) (8 * i.inputWordWidth + 31)

theorem rich_terminalCacheWidth_le {n : ℕ} (i : RationalPRGInput n) :
    i.richNativeSystem.terminalCacheWidth i.latticeDenominator ≤ i.sourceAndPackingWidth := by
  have hOne : rationalWordWidth (1 : ℚ) = 3 := by decide
  have hD := i.latticeDenominator_wordWidth
  change max (binaryWordWidth (n + 4)) (max (rationalWordWidth (1 : ℚ))
    (3 + 2 * binaryWordWidth i.latticeDenominator)) ≤ max (binaryWordWidth (n + 4)) (8 * i.inputWordWidth + 31)
  rw [hOne]
  omega

theorem poor_terminalCacheWidth_le {n : ℕ} (i : RationalPRGInput n) :
    i.poorNativeSystem.terminalCacheWidth i.latticeDenominator ≤ i.sourceAndPackingWidth := by
  have hB := i.budgetReader_wordWidth
  have hD := i.latticeDenominator_wordWidth
  change max (binaryWordWidth (n + 4)) (max (rationalWordWidth i.b)
    (3 + 2 * binaryWordWidth i.latticeDenominator)) ≤ max (binaryWordWidth (n + 4)) (8 * i.inputWordWidth + 31)
  omega

theorem richSharedPaperTerminalPreparationWork_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.sharedPaperTerminalPreparationWork model K bits ≤ (17 * n + 15) * model.rat i.sourceAndPackingWidth := by
  have h := i.richNativeSystem.sharedPaperTerminalPreparationWork_bound model i.latticeDenominator
    i.latticeDenominator_pos (le_refl _) i.lengths_on_lattice K bits
  exact h.trans (Nat.mul_le_mul_left _ (model.monotone i.rich_terminalCacheWidth_le))

theorem poorSharedPaperTerminalPreparationWork_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorNativeSystem.sharedPaperTerminalPreparationWork model K bits ≤ (17 * n + 15) * model.rat i.sourceAndPackingWidth := by
  have h := i.poorNativeSystem.sharedPaperTerminalPreparationWork_bound model i.latticeDenominator
    i.latticeDenominator_pos i.b_le i.lengths_on_lattice K bits
  exact h.trans (Nat.mul_le_mul_left _ (model.monotone i.poor_terminalCacheWidth_le))

def richSharedSourceAndPackingWork {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richSharedSourceProcessingAllowance model copyResources K bits + i.richNativeSystem.sharedPaperTerminalPreparationWork model K bits

def poorSharedSourceAndPackingWork {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorSharedSourceProcessingAllowance model copyResources K bits + i.poorNativeSystem.sharedPaperTerminalPreparationWork model K bits

theorem richSharedSourceAndPackingWork_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSharedSourceAndPackingWork model copyResources K bits ≤ (32 * n + 15) * model.rat i.sourceAndPackingWidth := by
  have hPrice := model.monotone (le_max_right (binaryWordWidth (n + 4)) (8 * i.inputWordWidth + 31))
  change model.rat (8 * i.inputWordWidth + 31) ≤ model.rat i.sourceAndPackingWidth at hPrice
  have hSource := (i.richSharedSourceProcessingAllowance_bound model copyResources K bits).trans
    (Nat.mul_le_mul_left (15 * n) hPrice)
  have hTerminal := i.richSharedPaperTerminalPreparationWork_bound model K bits
  unfold richSharedSourceAndPackingWork
  nlinarith

theorem poorSharedSourceAndPackingWork_logical_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedSourceAndPackingWork model false K bits ≤ (192 * n + 15) * model.rat i.sourceAndPackingWidth +
      (24 * i.inputWordWidth + 52) * (9 * n + 6 * K + 6002) := by
  have hPrice := model.monotone (le_max_right (binaryWordWidth (n + 4)) (8 * i.inputWordWidth + 31))
  change model.rat (8 * i.inputWordWidth + 31) ≤ model.rat i.sourceAndPackingWidth at hPrice
  have hSource := (i.poorSharedSourceProcessingAllowance_logical_bound model K bits).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (175 * n) hPrice) _)
  have hTerminal := i.poorSharedPaperTerminalPreparationWork_bound model K bits
  unfold poorSharedSourceAndPackingWork
  nlinarith

theorem poorSharedSourceAndPackingWork_fullCopy_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedSourceAndPackingWork model true K bits ≤ (2 * n * n + 188 * n + 15) * model.rat i.sourceAndPackingWidth +
      (24 * i.inputWordWidth + 52) * (9 * n + 6 * K + 6002) := by
  have hPrice := model.monotone (le_max_right (binaryWordWidth (n + 4)) (8 * i.inputWordWidth + 31))
  change model.rat (8 * i.inputWordWidth + 31) ≤ model.rat i.sourceAndPackingWidth at hPrice
  have hSource := (i.poorSharedSourceProcessingAllowance_fullCopy_bound model K bits).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * n * n + 171 * n) hPrice) _)
  have hTerminal := i.poorSharedPaperTerminalPreparationWork_bound model K bits
  unfold poorSharedSourceAndPackingWork
  nlinarith

end Blotto.RationalPRGInput
