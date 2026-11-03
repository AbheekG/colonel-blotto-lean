import Blotto.RationalNestedPreparationGuards

/-! Every second-profile construction keeps its family preparation before
the mirror guard, then prices the selected uniform mixture or padded branch.
The caller's outer block is unchanged. Factory multiplicity is separate. -/

namespace Blotto.RationalNestedInput

noncomputable def secondProfilePreparedBitCost (model : RationalCostModel) (primitive : ℕ → ℕ)
    (i : RationalNestedInput) (htu : i.u ≤ i.t) (K : ℕ) (outerBits : Fin K → Bool) : ℕ :=
  let f := i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outerBits
  i.scalarFieldBitCost model 0 3 +
    i.familyMidpointPreparedBitCost model primitive i.mirrorLength (i.mirrorLength_bounds htu).1
      (i.mirrorLength_bounds htu).2.1 K outerBits + i.mirrorGuardBitCost model +
    if hTt : i.mirrorLength < i.t then
      i.scalarFieldBitCost model 0 4 + i.secondUniformPreparedBitCost model htu hTt +
        RationalSegmentLottery.binaryPreparedBitCost model i.secondAlpha
          ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩ f (i.secondUniformLottery htu hTt)
    else f.paddingBitCost 9 0

theorem FieldsHeight.secondProfilePreparedBitCost_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (htu : i.u ≤ i.t)
    (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool) :
    i.secondProfilePreparedBitCost model primitive htu K outerBits ≤
      preparationNumericBitWork c K + 7655 * model.rat (preparationWidth s) := by
  let price := model.rat (preparationWidth s)
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have h8 : model.rat (1 + 2 * expressionHeightBudget s 8) ≤ price := model.heightPrice_mono (le_refl s) (by decide)
  have hMirror := (h.scalarFieldBitCost_bound hs model 0 hZero 3).trans (Nat.mul_le_mul_left 129 h8)
  have hGuard := (h.mirrorGuardBitCost_bound hs model).trans (Nat.mul_le_mul_left 132 h8)
  have hMirrorHeight := h.scalar hs 0 hZero 3
  change RationalHeight i.mirrorLength (expressionHeightBudget s 8) at hMirrorHeight
  have hFamily := h.familyMidpointPreparedBitCost_common hs model primitive c hPrimitive i.mirrorLength
    (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 hMirrorHeight K hK outerBits
  let f := i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outerBits
  have hF : f.HeightAt (expressionHeightBudget s 43) := h.familyLottery hs i.mirrorLength
    (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 hMirrorHeight K outerBits hK
  have hs43 := hs.trans (expressionHeightBudget_ge_input s 43)
  change i.familyMidpointPreparedBitCost model primitive i.mirrorLength (i.mirrorLength_bounds htu).1
    (i.mirrorLength_bounds htu).2.1 K outerBits ≤ preparationNumericBitWork c K + 3333 * price at hFamily
  change i.secondProfilePreparedBitCost model primitive htu K outerBits ≤ preparationNumericBitWork c K + 7655 * price
  unfold secondProfilePreparedBitCost
  dsimp only
  split
  · rename_i hTt
    have hAlpha := (h.scalarFieldBitCost_bound hs model 0 hZero 4).trans (Nat.mul_le_mul_left 129 h8)
    have hUniform := (h.secondUniformPreparedBitCost_bound hs model htu hTt).trans (Nat.mul_le_mul_left 3734
      (model.heightPrice_mono (le_refl s) (by decide : 28 ≤ 45)))
    have hA : RationalHeight i.secondAlpha (expressionHeightBudget s 43) := by
      have hp := h.scalar hs 0 hZero 4
      change RationalHeight i.secondAlpha (expressionHeightBudget s 8) at hp
      exact hp.mono (expressionHeightBudget_mono s (by decide : 8 ≤ 43))
    have hU := (h.secondUniform hs htu hTt).mono (expressionHeightBudget_mono s (by decide : 28 ≤ 43))
    have hMix := RationalSegmentLottery.binaryPreparedBitCost_bound model i.secondAlpha
      ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩ f (i.secondUniformLottery htu hTt)
      _ hs43 hA hF hU
    rw [expressionHeightBudget_comp] at hMix
    change RationalSegmentLottery.binaryPreparedBitCost model i.secondAlpha
      ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩ f (i.secondUniformLottery htu hTt) ≤ 198 * price at hMix
    change i.secondUniformPreparedBitCost model htu hTt ≤ 3734 * price at hUniform
    change i.scalarFieldBitCost model 0 3 + i.familyMidpointPreparedBitCost model primitive i.mirrorLength
      (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outerBits + i.mirrorGuardBitCost model +
      (i.scalarFieldBitCost model 0 4 + i.secondUniformPreparedBitCost model htu hTt +
        RationalSegmentLottery.binaryPreparedBitCost model i.secondAlpha
          ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩ f (i.secondUniformLottery htu hTt)) ≤
      preparationNumericBitWork c K + 7655 * price
    omega
  · have hPad := (f.paddingBitCost_bound model 9 0 _ hs43 hF).trans (Nat.mul_le_mul_left 126
      (model.heightPrice_mono (le_refl s) (by decide : 43 ≤ 45)))
    change f.paddingBitCost 9 0 ≤ 126 * price at hPad
    change i.scalarFieldBitCost model 0 3 + i.familyMidpointPreparedBitCost model primitive i.mirrorLength
      (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outerBits + i.mirrorGuardBitCost model +
        f.paddingBitCost 9 0 ≤ preparationNumericBitWork c K + 7655 * price
    omega

end Blotto.RationalNestedInput
