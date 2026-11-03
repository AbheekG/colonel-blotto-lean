import Blotto.RationalGluingCompleteData
import Blotto.RationalFourCallbackInvariant

/-! One reached-state data/primitive charge follows either actual ordered
four-variable branch. It includes decoded emission and local factory/copy/map
allowances, retaining the original controller states and cap. -/

namespace Blotto.RationalFourInput

noncomputable def fourCompleteDataCharge (i : RationalFourInput) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : FourSamplingState i → ℕ
  | .gluing hcase state => categoricalCallbackBitCost model state +
      (categoricalMachine (0 : Fin 81)).emissionCharge
        ((i.gluingDescriptor hcase).decodedInterpolationBitCost model primitive K scalarBits) state
  | .small hcase state => i.smallCompleteDataCharge hcase model primitive copyResources K outerBits scalarBits state

theorem FieldsHeight.fourCompleteDataCharge_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (cursor : FourSamplingState i) (hCursor : i.fourCallbackInvariant s cursor) :
    i.fourCompleteDataCharge model primitive copyResources K outerBits scalarBits cursor ≤
      28 * RationalNestedInput.preparationNumericBitWork c K + 210064 * model.rat (completeDataWidth s) := by
  cases cursor with
  | small hcase state =>
    exact h.smallCompleteDataCharge_bound hs hcase model primitive c hPrimitive copyResources K hPrecision
      outerBits scalarBits state hCursor
  | gluing hcase state =>
    let price := model.rat (completeDataWidth s)
    have hc := (categoricalCallbackBitCost_bound model state 81 _ hCursor).trans
      (Nat.mul_le_mul_left 659 (model.monotone (gluingCompleteDataWidth s)))
    change categoricalCallbackBitCost model state ≤ 659 * price at hc
    have hPoint : ∀ slot, (i.gluingDescriptor hcase).decodedInterpolationBitCost model primitive K scalarBits slot ≤
        RationalNestedInput.preparationNumericBitWork c K + 63 * price := by
      intro slot
      have hp := (h.gluingDescriptor hs hcase).decodedInterpolationBitCost_bound
        (hs.trans (expressionHeightBudget_ge_input s 36)) model primitive c hPrimitive K scalarBits slot
      rw [max_eq_left (hPrecision.trans (expressionHeightBudget_ge_input s 36)), expressionHeightBudget_comp] at hp
      have hMid : model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) ≤ price := model.heightPrice_mono hPrecision (by decide : 3 ≤ 73)
      have hMap : model.rat (1 + 2 * expressionHeightBudget s 39) ≤ price := model.heightPrice_mono (le_refl s) (by decide : 39 ≤ 73)
      change (i.gluingDescriptor hcase).decodedInterpolationBitCost model primitive K scalarBits slot ≤
        RationalNestedInput.preparationNumericBitWork c K + 11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
          52 * model.rat (1 + 2 * expressionHeightBudget s 39) at hp
      omega
    change categoricalCallbackBitCost model state + (categoricalMachine (0 : Fin 81)).emissionCharge
      ((i.gluingDescriptor hcase).decodedInterpolationBitCost model primitive K scalarBits) state ≤
        28 * RationalNestedInput.preparationNumericBitWork c K + 210064 * price
    unfold WordStateMachine.emissionCharge
    cases ht : (categoricalMachine (0 : Fin 81)).step state with
    | done slot =>
      have hp := hPoint slot
      change categoricalCallbackBitCost model state + (i.gluingDescriptor hcase).decodedInterpolationBitCost model primitive K scalarBits slot ≤ _
      omega
    | ask a b hb hab upper lower =>
      change categoricalCallbackBitCost model state + 0 ≤ _
      omega

end Blotto.RationalFourInput
