import Blotto.RationalNineSlotControlWork
import Blotto.RationalFourSpecCompleteProcessing

/-! Mixed terminal groups use the actual three-spec or four-spec compiler.
The two-group case retains separate machine/start descriptor construction;
the three-group case inherits the full unsorted four-variable allowance.
Packed input derivation, outer emission and metadata/backend remain separate. -/

namespace Blotto.RationalMixedGroupSpec
open scoped BigOperators

def threeStartWeightBitCost (i : RationalMixedGroupSpec 2) : ℕ :=
  2 * ∑ slot : Fin 9, rationalWordWidth (i.threeInput.segmentLottery.weight slot)

noncomputable def threeProcessingAllowance (i : RationalMixedGroupSpec 2) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  2 * (2 * RationalThreeSpecCode.inputFieldCopyBitCost i.threeInput + RationalThreeSpecCode.preparedSpecBitCost model i.threeInput) +
    i.threeStartWeightBitCost + i.threeInput.segmentLottery.dataAndCallbackBitWork model primitive 0 K scalarBits N bits pos hpos +
      i.threeInput.segmentLottery.nineBooleanControlWork K scalarBits N bits pos hpos

theorem FieldsHeight.threeProcessingAllowance_bound {i : RationalMixedGroupSpec 2} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.threeProcessingAllowance model primitive K scalarBits N bits pos hpos ≤
      RationalNestedInput.preparationNumericBitWork c K + 6675 * model.rat (RationalUniformGroupSpec.processingWidth (max s (K + 2))) +
        32 * RationalUniformGroupSpec.controlWordHeight (max s (K + 2)) +
          (24 * RationalUniformGroupSpec.controlWordHeight (max s (K + 2)) + 28) * (18 + 2 * (N - pos)) := by
  let w := max s (K + 2)
  let price := model.rat (RationalUniformGroupSpec.processingWidth w)
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hEnv := hW.three_environment
  have hTable := RationalThreeSpecCode.descriptor_height i.threeInput w hw hEnv
  have h18 : model.rat (1 + 2 * expressionHeightBudget w 18) ≤ price := model.heightPrice_mono (le_refl w) (by decide)
  have hCopy := (RationalThreeSpecCode.inputFieldCopyBitCost_bound model i.threeInput w hEnv).trans
    (Nat.mul_le_mul_left 5 ((model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input w 18)) 1)).trans h18))
  have hPrep := (RationalThreeSpecCode.preparedSpecBitCost_bound model i.threeInput w hw hEnv).trans (Nat.mul_le_mul_left 2920 h18)
  have hStart : i.threeStartWeightBitCost ≤ 18 * price := by
    have hp : (∑ slot : Fin 9, rationalWordWidth (i.threeInput.segmentLottery.weight slot)) ≤ 9 * price := by
      calc
        _ ≤ ∑ _slot : Fin 9, price := Finset.sum_le_sum (fun slot _ =>
          (rationalWordWidth_of_height (hTable.1 slot)).trans ((model.word_le _).trans h18))
        _ = _ := by simp
    unfold threeStartWeightBitCost
    omega
  have hData := hTable.dataAndCallbackBitWork_bound (hw.trans (expressionHeightBudget_ge_input w 18))
    model primitive c hPrimitive 0 K scalarBits N bits pos hpos
  rw [max_eq_left ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 18)), expressionHeightBudget_comp] at hData
  have hCat : model.rat (categoricalRequestWidth 9 (expressionHeightBudget w 18)) ≤ price :=
    model.monotone (RationalUniformGroupSpec.processingWidth_categorical w)
  have hMid : model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) ≤ price := model.heightPrice_mono (le_max_right s (K + 2)) (by decide : 3 ≤ 23)
  have hPoint : model.rat (1 + 2 * expressionHeightBudget w 21) ≤ price := model.heightPrice_mono (le_refl w) (by decide)
  have hControl := hTable.nineBooleanControlWork_bound K scalarBits N bits pos hpos
  change i.threeInput.segmentLottery.dataAndCallbackBitWork model primitive 0 K scalarBits N bits pos hpos ≤
    747 * model.rat (categoricalRequestWidth 9 (expressionHeightBudget w 18)) +
      (RationalNestedInput.preparationNumericBitWork c K + 11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
        39 * model.rat (1 + 2 * expressionHeightBudget w 21)) at hData
  change i.threeInput.segmentLottery.nineBooleanControlWork K scalarBits N bits pos hpos ≤
    32 * RationalUniformGroupSpec.controlWordHeight w +
      (24 * RationalUniformGroupSpec.controlWordHeight w + 28) * (18 + 2 * (N - pos)) at hControl
  change i.threeProcessingAllowance model primitive K scalarBits N bits pos hpos ≤
    RationalNestedInput.preparationNumericBitWork c K + 6675 * price +
      32 * RationalUniformGroupSpec.controlWordHeight w +
        (24 * RationalUniformGroupSpec.controlWordHeight w + 28) * (18 + 2 * (N - pos))
  unfold threeProcessingAllowance
  omega

noncomputable def completeProcessingAllowance {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ := by
  by_cases h2 : m = 2
  · subst m
    exact i.threeProcessingAllowance model primitive K scalarBits N bits pos hpos
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.fourInput.completeProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.completeProcessingAllowance_bound {m : ℕ} {i : RationalMixedGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.completeProcessingAllowance hm model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        70000000 * model.rat (RationalFourInput.completeDataWidth (max s (K + 2))) +
          320 * RationalFourInput.fourControlWordHeight (max s (K + 2)) +
            (24 * RationalFourInput.fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) := by
  rcases hm with rfl | rfl
  · have hp := h.threeProcessingAllowance_bound hs model primitive c hPrimitive K scalarBits N bits pos hpos
    let w := max s (K + 2)
    have hPrice := model.heightPrice_mono (le_refl w) (by decide : 23 ≤ 73)
    change model.rat (RationalUniformGroupSpec.processingWidth w) ≤ model.rat (RationalFourInput.completeDataWidth w) at hPrice
    have hHeight : RationalUniformGroupSpec.controlWordHeight w ≤ RationalFourInput.fourControlWordHeight w := by
      have hm := expressionHeightBudget_mono w (by decide : 18 ≤ 68)
      unfold RationalUniformGroupSpec.controlWordHeight RationalFourInput.fourControlWordHeight
      nlinarith
    change i.threeProcessingAllowance model primitive K scalarBits N bits pos hpos ≤ _
    nlinarith
  · have hp := h.fourCompleteProcessingAllowance_bound hs model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos
    change i.fourInput.completeProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos ≤ _
    omega

end Blotto.RationalMixedGroupSpec
