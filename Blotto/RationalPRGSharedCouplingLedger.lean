import Blotto.RationalLottoSharedCouplingWork
import Blotto.RationalPRGOutputHeight
import Blotto.RationalPRGSharedTerminalLedger
import Blotto.RationalPaperFallbackCost

/-! Prices terminal coupling and fallback on the primary paper packet, then
adds the already verified source/packing allowance. This is a labelled work
ledger; metadata, physical ownership and a concrete backend remain separate. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedPaperCouplingWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedCouplingAndEmissionWork model primitive copyResources K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

def paperFallbackWork {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.paperFallbackBitWork K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

-- Constant expression-depth inflation is explicit and independent of n.
def paperCouplingWidth {n : ℕ} (i : RationalPRGInput n) (K : ℕ) : ℕ :=
  1 + 2 * expressionHeightBudget (max (3 + i.inputWordWidth) (K + 2)) 75

def paperCouplingControlHeight {n : ℕ} (i : RationalPRGInput n) (K : ℕ) : ℕ :=
  RationalTerminalLotto.terminalCouplingWordHeight (max (3 + i.inputWordWidth) (K + 2))

def paperCouplingBound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) (c K : ℕ) : ℕ :=
  9072 * RationalNestedInput.preparationNumericBitWork c K +
    (70000020 + 8 * n) * model.rat (i.paperCouplingWidth K) +
      320 * i.paperCouplingControlHeight K + (24 * i.paperCouplingControlHeight K + 28) *
        (162 + 2 * RationalLottoResourceSystem.coinBitBudget n K)

theorem sharedPaperCouplingWork_bounds {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.sharedPaperCouplingWork model primitive copyResources K bits ≤ i.paperCouplingBound model c K ∧
      i.poorNativeSystem.sharedPaperCouplingWork model primitive copyResources K bits ≤ i.paperCouplingBound model c K := by
  have hs : 2 ≤ 3 + i.inputWordWidth := by omega
  have hWidth : binaryWordWidth i.latticeDenominator ≤ 3 + i.inputWordWidth :=
    i.latticeDenominator_wordWidth.trans (by omega)
  have hOne : RationalHeight (1 : ℚ) (3 + i.inputWordWidth) :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hBudget : RationalHeight i.b (3 + i.inputWordWidth) :=
    (rationalHeight_of_wordWidth i.b).mono (by unfold inputWordWidth; omega)
  exact ⟨i.richNativeSystem_on_lattice.sharedCouplingAndEmissionWork_bound i.latticeDenominator_pos
      le_rfl _ hs hOne hWidth model primitive c hPrimitive copyResources K _ _ _ _,
    i.poorNativeSystem_on_lattice.sharedCouplingAndEmissionWork_bound i.latticeDenominator_pos
      i.b_le _ hs hBudget hWidth model primitive c hPrimitive copyResources K _ _ _ _⟩

theorem paperFallbackWork_bounds {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.paperFallbackWork K bits ≤ 2 * n * model.rat (1 + 2 * (3 + i.inputWordWidth)) ∧
      i.poorNativeSystem.paperFallbackWork K bits ≤ 2 * n * model.rat (1 + 2 * (3 + i.inputWordWidth)) := by
  have hs : 2 ≤ 3 + i.inputWordWidth := by omega
  have hOne : RationalHeight (1 : ℚ) (3 + i.inputWordWidth) :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hBudget : RationalHeight i.b (3 + i.inputWordWidth) :=
    (rationalHeight_of_wordWidth i.b).mono (by unfold inputWordWidth; omega)
  exact ⟨i.richNativeSystem.paperFallbackBitWork_bound model _ hs hOne K _ _ _ _,
    i.poorNativeSystem.paperFallbackBitWork_bound model _ hs hBudget K _ _ _ _⟩

end Blotto.RationalPRGInput
