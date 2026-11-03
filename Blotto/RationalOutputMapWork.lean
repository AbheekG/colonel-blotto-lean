import Blotto.RationalReflectionOutputCost
import Blotto.RationalFourPermutationCost
import Blotto.RationalReflectedLocalProcessing
import Blotto.RationalFourSpecHeight
import Blotto.CachedEmissionBounds

/-! The maintained reflection/permutation output maps receive explicit
one-time rational prices on the actual pre-map emitted values. These prices
assume available input coordinates; uncached producer rereads and metadata/
backend costs remain separate from the map's own arithmetic/copy component. -/

namespace Blotto.RationalFourInput

def reflectedMapBitWork (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  ((i.reflectedResourceSystem hcase).machine K outerBits scalarBits).cachedEmissionWork
    (RationalReflectionCode.outputBitCost model i.originalLengths)
    N bits (.state (i.reflectedResourceSystem hcase).samplingStart) pos hpos

theorem FieldsHeight.reflectedMapBitWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.reflectedMapBitWork hcase model K outerBits scalarBits N bits pos hpos ≤
      64 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 72) := by
  let w := max s (K + 2)
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hSystem := hW.reflectedResourceSystem hw hcase
  have hMachine := hSystem.machine_leaves (hw.trans (expressionHeightBudget_ge_input w 14)) K outerBits scalarBits
  rw [max_eq_left ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 14)), expressionHeightBudget_comp] at hMachine
  apply WordStateMachine.cachedEmissionWork_leaves_bound
  apply WordChoiceTree.forLeaves_mono _ _ _ _ hMachine
  intro x hx
  have hp := RationalReflectionCode.outputBitCost_bound model i.originalLengths x _
    (hw.trans (expressionHeightBudget_ge_input w 71))
    (fun j => (hW.originalLengths j).mono (expressionHeightBudget_ge_input w 71)) hx
  simpa only [expressionHeightBudget_comp] using hp

theorem reflectedMapBitWork_of_none (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N)
    (hNone : (((i.reflectedResourceSystem hcase).machine K outerBits scalarBits).runCachedIndexed N bits
      (.state (i.reflectedResourceSystem hcase).samplingStart) pos hpos).1 = none) :
    i.reflectedMapBitWork hcase model K outerBits scalarBits N bits pos hpos = 0 :=
  ((i.reflectedResourceSystem hcase).machine K outerBits scalarBits).cachedEmissionWork_of_none _
    N bits (.state (i.reflectedResourceSystem hcase).samplingStart) pos hpos hNone

end Blotto.RationalFourInput
namespace Blotto.RationalFourSpec

def permutationBitWork (i : RationalFourSpec) (model : RationalCostModel) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.input.machine K outerBits scalarBits).cachedEmissionWork (RationalFourPermutationCode.outputBitCost model i.permutation)
    N bits (.state (i.input.start K outerBits scalarBits)) pos hpos

theorem FieldsHeight.permutationBitWork_bound {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.permutationBitWork model K outerBits scalarBits N bits pos hpos ≤
      80 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 72) := by
  have hMachine := h.input.machine_leaves hs K outerBits scalarBits
  apply WordStateMachine.cachedEmissionWork_leaves_bound
  apply WordChoiceTree.forLeaves_mono _ _ _ _ hMachine
  intro x hx
  exact RationalFourPermutationCode.outputBitCost_bound model i.permutation x _
    (hs.trans ((le_max_left s (K + 2)).trans (expressionHeightBudget_ge_input _ 72))) hx

theorem permutationBitWork_of_none (i : RationalFourSpec) (model : RationalCostModel) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N)
    (hNone : ((i.input.machine K outerBits scalarBits).runCachedIndexed N bits
      (.state (i.input.start K outerBits scalarBits)) pos hpos).1 = none) :
    i.permutationBitWork model K outerBits scalarBits N bits pos hpos = 0 :=
  (i.input.machine K outerBits scalarBits).cachedEmissionWork_of_none _ N bits
    (.state (i.input.start K outerBits scalarBits)) pos hpos hNone

end Blotto.RationalFourSpec
