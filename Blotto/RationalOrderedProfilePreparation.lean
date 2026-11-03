import Blotto.RationalSecondProfilePreparation
import Blotto.RationalThirdProfilePreparation

/-! All ordered interior nested profile branches share one construction
envelope. Actual numerical guard operands, zero weights and padding are kept.
This prices one invocation, not its frequency in a serial continuation. -/

namespace Blotto.RationalNestedInput

noncomputable def profilePreparedBitCost (model : RationalCostModel) (primitive : ℕ → ℕ)
    (i : RationalNestedInput) (K : ℕ) (outerBits : Fin K → Bool) : ℕ :=
  i.lengthGuardBitCost model true i.t + if htv : i.t ≤ i.v then
    i.firstMidpointPreparedBitCost model primitive htv K outerBits +
      (i.firstConditionalLottery htv (i.midpointLocation K outerBits) (i.midpointLocation_bounds K outerBits)).paddingBitCost 9 0
  else i.lengthGuardBitCost model false i.t + if htu : i.u ≤ i.t then
    i.secondProfilePreparedBitCost model primitive htu K outerBits
  else i.thirdProfilePreparedBitCost model primitive (lt_of_not_ge htv) (lt_of_not_ge htu) K outerBits

theorem FieldsHeight.profilePreparedBitCost_common {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool) :
    i.profilePreparedBitCost model primitive K outerBits ≤
      preparationNumericBitWork c K + 7800 * model.rat (preparationWidth s) := by
  let price := model.rat (preparationWidth s)
  have h1 : model.rat (1 + 2 * expressionHeightBudget s 1) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have hT := h.2.2.2.2.1
  have hGuardV := (h.lengthGuardBitCost_bound hs model true i.t hT).trans (Nat.mul_le_mul_left 7 h1)
  have hGuardU := (h.lengthGuardBitCost_bound hs model false i.t hT).trans (Nat.mul_le_mul_left 7 h1)
  change i.profilePreparedBitCost model primitive K outerBits ≤ preparationNumericBitWork c K + 7800 * price
  unfold profilePreparedBitCost
  split
  · rename_i htv
    have hp := h.firstMidpointPreparedBitCost_common hs model primitive c hPrimitive htv K hK outerBits
    change i.firstMidpointPreparedBitCost model primitive htv K outerBits ≤ preparationNumericBitWork c K + 3199 * price at hp
    have hTable := h.firstMidpoint hs htv K outerBits
    rw [max_eq_left hK] at hTable
    have hPad := ((i.firstConditionalLottery htv (i.midpointLocation K outerBits)
      (i.midpointLocation_bounds K outerBits)).paddingBitCost_bound model 9 0 _
        (hs.trans (expressionHeightBudget_ge_input s 27)) hTable).trans (Nat.mul_le_mul_left 126
          (model.heightPrice_mono (le_refl s) (by decide : 27 ≤ 45)))
    change (i.firstConditionalLottery htv (i.midpointLocation K outerBits)
      (i.midpointLocation_bounds K outerBits)).paddingBitCost 9 0 ≤ 126 * price at hPad
    omega
  · split
    · rename_i htv htu
      have hp := h.secondProfilePreparedBitCost_bound hs model primitive c hPrimitive htu K hK outerBits
      change i.secondProfilePreparedBitCost model primitive htu K outerBits ≤ preparationNumericBitWork c K + 7655 * price at hp
      omega
    · rename_i htv htu
      have hp := h.thirdProfilePreparedBitCost_bound hs model primitive c hPrimitive
        (lt_of_not_ge htv) (lt_of_not_ge htu) K hK outerBits
      change i.thirdProfilePreparedBitCost model primitive (lt_of_not_ge htv) (lt_of_not_ge htu) K outerBits ≤
        preparationNumericBitWork c K + 4512 * price at hp
      omega

theorem FieldsHeight.profilePreparedBitCost_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits : Fin K → Bool) :
    i.profilePreparedBitCost model primitive K outerBits ≤
      preparationNumericBitWork c K + 7800 * model.rat (preparationWidth (max s (K + 2))) :=
  (h.mono (le_max_left _ _)).profilePreparedBitCost_common (hs.trans (le_max_left _ _))
    model primitive c hPrimitive K (le_max_right _ _) outerBits

end Blotto.RationalNestedInput
