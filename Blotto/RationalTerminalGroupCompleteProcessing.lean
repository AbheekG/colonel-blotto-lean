import Blotto.RationalMixedGroupCompleteProcessing
import Blotto.RationalTerminalEmissionWork

/-! The actual packed terminal compiler selects a uniform or mixed group
program at the same caller cap/position. Local construction/processing and
cached route emission are separately priced. Packing, raw input decoding and
metadata/backend/ownership remain outside this terminal coupling component. -/

namespace Blotto.RationalTerminalLotto

def terminalCouplingWordHeight (s : ℕ) : ℕ := (expressionHeightBudget s 69 + 1) * 82

def terminalCouplingDataWidth (s : ℕ) : ℕ := 1 + 2 * expressionHeightBudget s 74

noncomputable def groupCoreProcessingAllowance {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let packed := RationalTerminalPacking.prepare i
  match h : i.pivot with
  | none => (packed.uniformSpec (i.pivot_none h)).completeProcessingAllowance i.groups_count
      model primitive K scalarBits N bits pos hpos
  | some pivot => (packed.mixedSpec pivot (i.pivot_some h)).completeProcessingAllowance i.groups_count
      model primitive copyResources K outerBits scalarBits N bits pos hpos

theorem OnLattice.groupCoreProcessingAllowance_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.groupCoreProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        70000000 * model.rat (terminalCouplingDataWidth (max s (K + 2))) +
          320 * terminalCouplingWordHeight (max s (K + 2)) +
            (24 * terminalCouplingWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) := by
  let w := max s (K + 2)
  let price := model.rat (terminalCouplingDataWidth w)
  let H := terminalCouplingWordHeight w
  have hw := hs.trans (le_max_left s (K + 2))
  have hBudgetW := hBudget.mono (le_max_left s (K + 2))
  have hWidthW := hWidth.trans (le_max_left s (K + 2))
  unfold groupCoreProcessingAllowance
  dsimp only
  split
  · rename_i hNone
    rw [RationalTerminalPacking.uniformSpec_eq]
    have hp := (h.uniformSpec hD hB w hBudgetW hWidthW (i.pivot_none hNone)).completeProcessingAllowance_bound
      hw i.groups_count model primitive c hPrimitive K scalarBits N bits pos hpos
    rw [max_eq_left (le_max_right s (K + 2))] at hp
    have hPrice : model.rat (RationalUniformGroupSpec.processingWidth w) ≤ price := model.heightPrice_mono (le_refl w) (by decide : 23 ≤ 74)
    have hHeight : RationalUniformGroupSpec.controlWordHeight w ≤ H := by
      have hm := expressionHeightBudget_mono w (by decide : 18 ≤ 69)
      unfold RationalUniformGroupSpec.controlWordHeight
      dsimp [H, terminalCouplingWordHeight]
      nlinarith
    change (i.uniformSpec (i.pivot_none hNone)).completeProcessingAllowance i.groups_count model primitive K scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K + 70000000 * price +
        320 * H + (24 * H + 28) * (162 + 2 * (N - pos))
    nlinarith
  · rename_i pivot hSome
    rw [RationalTerminalPacking.mixedSpec_eq]
    have hm := expressionHeightBudget_ge_input w 1
    have hp := (h.mixedSpec hD hB w hBudgetW hWidthW pivot (i.pivot_some hSome)).completeProcessingAllowance_bound
      (hw.trans hm) i.groups_count model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos
    rw [max_eq_left ((le_max_right s (K + 2)).trans hm)] at hp
    unfold RationalFourInput.completeDataWidth RationalFourInput.fourControlWordHeight at hp
    simp only [expressionHeightBudget_comp] at hp
    exact hp

noncomputable def couplingAndEmissionAllowance {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.groupCoreProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.emissionBitWork model K outerBits scalarBits N bits pos hpos

theorem OnLattice.couplingAndEmissionAllowance_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.couplingAndEmissionAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        (70000004 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 75) +
          320 * terminalCouplingWordHeight (max s (K + 2)) +
            (24 * terminalCouplingWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) := by
  have hCore := (h.groupCoreProcessingAllowance_bound hD hB s hs hBudget hWidth model primitive c hPrimitive copyResources K
    outerBits scalarBits N bits pos hpos)
  have hEmit := h.emissionBitWork_bound hD hB s hs hBudget hWidth model K outerBits scalarBits N bits pos hpos
  have hPrice := model.heightPrice_mono (le_refl (max s (K + 2))) (by decide : 74 ≤ 75)
  change model.rat (terminalCouplingDataWidth (max s (K + 2))) ≤
    model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 75) at hPrice
  unfold couplingAndEmissionAllowance
  nlinarith

end Blotto.RationalTerminalLotto
