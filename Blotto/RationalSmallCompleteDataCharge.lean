import Blotto.RationalNestedReachedDataCharge
import Blotto.RationalNestedReachedOutputHeight
import Blotto.RationalReflectionOutputCost
import Blotto.RationalSmallCallbackInvariant

/-! The small-case binary controller prices both branch callbacks on its own
path. Dense reflection keeps four producer-price allowances. Construction,
Boolean control, later maps and metadata/backend/ownership are separate. -/

namespace Blotto.RationalFourInput

def completeDataWidth (s : ℕ) : ℕ := 1 + 2 * expressionHeightBudget s 73

theorem completeDataWidth_components (s : ℕ) :
    categoricalRequestWidth 9 (expressionHeightBudget s 35) ≤ completeDataWidth s ∧
      1 + 2 * expressionHeightBudget s 38 ≤ completeDataWidth s ∧
        1 + 2 * expressionHeightBudget s 15 ≤ completeDataWidth s := by
  have h40 : expressionHeightBudget s 40 = 32 * expressionHeightBudget s 35 + 31 := by
    rw [show 40 = 35 + 5 by decide, ← expressionHeightBudget_comp]
    change (expressionHeightBudget s 35 + 1) * 32 - 1 = _
    omega
  have h40le := expressionHeightBudget_mono s (by decide : 40 ≤ 73)
  have h38le := expressionHeightBudget_mono s (by decide : 38 ≤ 73)
  have h15le := expressionHeightBudget_mono s (by decide : 15 ≤ 73)
  unfold completeDataWidth categoricalRequestWidth
  omega

def smallUniformFullCharge (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (K : ℕ) (scalarBits : Fin K → Bool)
    (state : CategoricalState (Fin 9)) : ℕ :=
  categoricalCallbackBitCost model state + (categoricalMachine (0 : Fin 9)).emissionCharge
    ((i.smallUniformLottery hcase).decodedInterpolationBitCost model primitive K scalarBits) state

noncomputable def smallReflectedFullCharge (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (state : (i.reflectedResourceSystem hcase).SamplingState) : ℕ :=
  let system := i.reflectedResourceSystem hcase
  4 * system.localDataOutputCharge model primitive copyResources K outerBits scalarBits state +
    (system.machine K outerBits scalarBits).emissionCharge (RationalReflectionCode.outputBitCost model i.originalLengths) state

noncomputable def smallCompleteDataCharge (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : i.SmallState hcase → ℕ :=
  binaryCallbackCharge i.smallRootFieldBitCost (i.smallUniformFullCharge hcase model primitive K scalarBits)
    (i.smallReflectedFullCharge hcase model primitive copyResources K outerBits scalarBits)

theorem FieldsHeight.smallUniformFullCharge_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (scalarBits : Fin K → Bool) (state : CategoricalState (Fin 9)) (hState : state.Bounded 9 (expressionHeightBudget s 35)) :
    i.smallUniformFullCharge hcase model primitive K scalarBits state ≤
      RationalNestedInput.preparationNumericBitWork c K + 146 * model.rat (completeDataWidth s) := by
  let price := model.rat (completeDataWidth s)
  have widths := completeDataWidth_components s
  have hc := (categoricalCallbackBitCost_bound model state 9 _ hState).trans (Nat.mul_le_mul_left 83 (model.monotone widths.1))
  have hPoint : ∀ slot, (i.smallUniformLottery hcase).decodedInterpolationBitCost model primitive K scalarBits slot ≤
      RationalNestedInput.preparationNumericBitWork c K + 63 * price := by
    intro slot
    have hp := (h.smallUniformLottery hs hcase).decodedInterpolationBitCost_bound
      (hs.trans (expressionHeightBudget_ge_input s 35)) model primitive c hPrimitive K scalarBits slot
    rw [max_eq_left (hPrecision.trans (expressionHeightBudget_ge_input s 35)), expressionHeightBudget_comp] at hp
    have hMid : model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) ≤ price := model.heightPrice_mono hPrecision (by decide : 3 ≤ 73)
    have hMap := model.monotone widths.2.1
    change (i.smallUniformLottery hcase).decodedInterpolationBitCost model primitive K scalarBits slot ≤
      RationalNestedInput.preparationNumericBitWork c K + 11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
        52 * model.rat (1 + 2 * expressionHeightBudget s 38) at hp
    change model.rat (1 + 2 * expressionHeightBudget s 38) ≤ price at hMap
    omega
  change categoricalCallbackBitCost model state ≤ 83 * price at hc
  unfold smallUniformFullCharge WordStateMachine.emissionCharge
  cases ht : (categoricalMachine (0 : Fin 9)).step state with
  | done slot =>
    have hp := hPoint slot
    change categoricalCallbackBitCost model state +
      (i.smallUniformLottery hcase).decodedInterpolationBitCost model primitive K scalarBits slot ≤
        RationalNestedInput.preparationNumericBitWork c K + 146 * price
    omega
  | ask a b hb hab upper lower =>
    change categoricalCallbackBitCost model state + 0 ≤ RationalNestedInput.preparationNumericBitWork c K + 146 * price
    omega

theorem FieldsHeight.smallReflectedFullCharge_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (state : (i.reflectedResourceSystem hcase).SamplingState)
    (hState : (i.reflectedResourceSystem hcase).LocalCallbackInvariant (expressionHeightBudget s 14) state) :
    i.smallReflectedFullCharge hcase model primitive copyResources K outerBits scalarBits state ≤
      28 * RationalNestedInput.preparationNumericBitWork c K + 210064 * model.rat (completeDataWidth s) := by
  let system := i.reflectedResourceSystem hcase
  let price := model.rat (completeDataWidth s)
  have hSystem := h.reflectedResourceSystem hs hcase
  have hs14 := hs.trans (expressionHeightBudget_ge_input s 14)
  have hPrecision14 := hPrecision.trans (expressionHeightBudget_ge_input s 14)
  have hd := hSystem.localDataOutputCharge_bound hs14 model primitive c hPrimitive copyResources K hPrecision14
    outerBits scalarBits state hState
  unfold RationalNestedResourceSystem.localDataOutputWidth at hd
  rw [expressionHeightBudget_comp] at hd
  change system.localDataOutputCharge model primitive copyResources K outerBits scalarBits state ≤
    7 * RationalNestedInput.preparationNumericBitWork c K + 52500 * price at hd
  have hp := hSystem.localOutputHeight_post hs14 K hPrecision14 outerBits scalarBits state hState
  have hMap : (system.machine K outerBits scalarBits).emissionCharge (RationalReflectionCode.outputBitCost model i.originalLengths) state ≤ 64 * price := by
    unfold WordStateMachine.emissionCharge
    cases ht : (system.machine K outerBits scalarBits).step state with
    | done x =>
      rw [ht] at hp
      have hHeight : ∀ j, RationalHeight (x j) (expressionHeightBudget s 71) := by
        simpa only [expressionHeightBudget_comp] using hp
      have hm := RationalReflectionCode.outputBitCost_bound model i.originalLengths x _
        (hs.trans (expressionHeightBudget_ge_input s 71))
        (fun j => (h.originalLengths j).mono (expressionHeightBudget_ge_input s 71)) hHeight
      rw [expressionHeightBudget_comp] at hm
      exact hm.trans (Nat.mul_le_mul_left 64 (model.heightPrice_mono (le_refl s) (by decide : 72 ≤ 73)))
    | ask a b hb hab upper lower => exact Nat.zero_le _
  change i.smallReflectedFullCharge hcase model primitive copyResources K outerBits scalarBits state ≤
    28 * RationalNestedInput.preparationNumericBitWork c K + 210064 * price
  unfold smallReflectedFullCharge
  dsimp only
  change 4 * system.localDataOutputCharge model primitive copyResources K outerBits scalarBits state +
    (system.machine K outerBits scalarBits).emissionCharge (RationalReflectionCode.outputBitCost model i.originalLengths) state ≤
      28 * RationalNestedInput.preparationNumericBitWork c K + 210064 * price
  omega

theorem FieldsHeight.smallCompleteDataCharge_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (cursor : i.SmallState hcase) (hCursor : i.smallCallbackInvariant hcase s cursor) :
    i.smallCompleteDataCharge hcase model primitive copyResources K outerBits scalarBits cursor ≤
      28 * RationalNestedInput.preparationNumericBitWork c K + 210064 * model.rat (completeDataWidth s) := by
  cases cursor with
  | start =>
    have hWord := (rationalWordWidth_of_height h.2.2.2.2.2).trans ((model.word_le _).trans
      (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input s 73)) 1)))
    have hp := ProbabilityWords.ofRatBitCost_eq i.p ⟨i.p_pos.le, i.p_lt.le⟩
    change rationalWordWidth i.p ≤ model.rat (completeDataWidth s) at hWord
    change i.smallRootFieldBitCost = 2 * rationalWordWidth i.p - 1 at hp
    change i.smallCompleteDataCharge hcase model primitive copyResources K outerBits scalarBits BinaryState.start ≤ _
    change i.smallRootFieldBitCost ≤ _
    omega
  | upper state =>
    have hp := h.smallUniformFullCharge_bound hs hcase model primitive c hPrimitive K hPrecision scalarBits state hCursor
    change i.smallUniformFullCharge hcase model primitive K scalarBits state ≤ _
    omega
  | lower state => exact h.smallReflectedFullCharge_bound hs hcase model primitive c hPrimitive copyResources K hPrecision outerBits scalarBits state hCursor

end Blotto.RationalFourInput
