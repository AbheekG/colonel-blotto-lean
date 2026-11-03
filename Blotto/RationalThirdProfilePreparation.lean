import Blotto.RationalNestedPreparationGuards

/-! Third profiles construct the residual before the length guard. The
positive-length branch adds a fixed-mean family and mixture; zero length pads
the residual. All written zero-weight fields are retained and priced. -/

namespace Blotto.RationalNestedInput

noncomputable def thirdProfilePreparedBitCost (model : RationalCostModel) (primitive : ℕ → ℕ)
    (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) (outerBits : Fin K → Bool) : ℕ :=
  let r := (i.residualInput hvt htu).segmentLottery.padRight 6 0
  i.paddedResidualPreparedBitCost model hvt htu + i.lengthGuardBitCost model true 0 +
    if hv : 0 < i.v then
      i.lengthFieldBitCost model true + i.familyMidpointPreparedBitCost model primitive i.v hv le_rfl K outerBits +
        i.scalarFieldBitCost model 0 5 + RationalSegmentLottery.binaryPreparedBitCost model i.thirdAlpha
          ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
          (i.familyLottery i.v hv le_rfl K outerBits) r
    else r.paddingBitCost 9 0

theorem FieldsHeight.thirdProfilePreparedBitCost_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (hvt : i.v < i.t) (htu : i.t < i.u)
    (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool) :
    i.thirdProfilePreparedBitCost model primitive hvt htu K outerBits ≤
      preparationNumericBitWork c K + 4512 * model.rat (preparationWidth s) := by
  let price := model.rat (preparationWidth s)
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have h1 : model.rat (1 + 2 * expressionHeightBudget s 1) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have hResidual := (h.paddedResidualPreparedBitCost_bound hs model hvt htu).trans (Nat.mul_le_mul_left 841
    (model.heightPrice_mono (le_refl s) (by decide : 10 ≤ 45)))
  have hGuard := (h.lengthGuardBitCost_bound hs model true 0 hZero).trans (Nat.mul_le_mul_left 7 h1)
  change i.paddedResidualPreparedBitCost model hvt htu ≤ 841 * price at hResidual
  let r := (i.residualInput hvt htu).segmentLottery.padRight 6 0
  have hs10 := hs.trans (expressionHeightBudget_ge_input s 10)
  have hR : r.HeightAt (expressionHeightBudget s 10) := (h.residual hs hvt htu).padRight hs10 6 0
  change i.thirdProfilePreparedBitCost model primitive hvt htu K outerBits ≤ preparationNumericBitWork c K + 4512 * price
  unfold thirdProfilePreparedBitCost
  dsimp only
  split
  · rename_i hv
    have hValue := (h.lengthFieldBitCost_bound hs model true).trans (Nat.mul_le_mul_left 4 h1)
    have hV := h.v.mono (expressionHeightBudget_mono s (by decide : 1 ≤ 8))
    have hFamily := h.familyMidpointPreparedBitCost_common hs model primitive c hPrimitive i.v hv le_rfl hV K hK outerBits
    have hAlpha := (h.scalarFieldBitCost_bound hs model 0 hZero 5).trans (Nat.mul_le_mul_left 129
      (model.heightPrice_mono (le_refl s) (by decide : 8 ≤ 45)))
    change i.scalarFieldBitCost model 0 5 ≤ 129 * price at hAlpha
    have hF := h.familyLottery hs i.v hv le_rfl hV K outerBits hK
    have hA : RationalHeight i.thirdAlpha (expressionHeightBudget s 43) := by
      have hp := h.scalar hs 0 hZero 5
      change RationalHeight i.thirdAlpha (expressionHeightBudget s 8) at hp
      exact hp.mono (expressionHeightBudget_mono s (by decide : 8 ≤ 43))
    have hs43 := hs.trans (expressionHeightBudget_ge_input s 43)
    have hMix := RationalSegmentLottery.binaryPreparedBitCost_bound model i.thirdAlpha
      ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
      (i.familyLottery i.v hv le_rfl K outerBits) r _ hs43 hA hF
      (hR.mono (expressionHeightBudget_mono s (by decide : 10 ≤ 43)))
    rw [expressionHeightBudget_comp] at hMix
    change RationalSegmentLottery.binaryPreparedBitCost model i.thirdAlpha
      ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
      (i.familyLottery i.v hv le_rfl K outerBits) r ≤ 198 * price at hMix
    change i.familyMidpointPreparedBitCost model primitive i.v hv le_rfl K outerBits ≤
      preparationNumericBitWork c K + 3333 * price at hFamily
    change i.paddedResidualPreparedBitCost model hvt htu + i.lengthGuardBitCost model true 0 +
      (i.lengthFieldBitCost model true + i.familyMidpointPreparedBitCost model primitive i.v hv le_rfl K outerBits +
        i.scalarFieldBitCost model 0 5 + RationalSegmentLottery.binaryPreparedBitCost model i.thirdAlpha
          ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
          (i.familyLottery i.v hv le_rfl K outerBits) r) ≤ preparationNumericBitWork c K + 4512 * price
    omega
  · have hPad := (r.paddingBitCost_bound model 9 0 _ hs10 hR).trans (Nat.mul_le_mul_left 126
      (model.heightPrice_mono (le_refl s) (by decide : 10 ≤ 45)))
    change r.paddingBitCost 9 0 ≤ 126 * price at hPad
    change i.paddedResidualPreparedBitCost model hvt htu + i.lengthGuardBitCost model true 0 + r.paddingBitCost 9 0 ≤
      preparationNumericBitWork c K + 4512 * price
    omega

end Blotto.RationalNestedInput
