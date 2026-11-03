import Blotto.RationalSecondUniformMetadata

/-! The second profile retains family preparation before its mirror guard.
Two mirror evaluations and the selected alpha/uniform/mixture or padding costs
stay explicit. The common envelope conservatively retains either branch. -/

namespace Blotto.RationalNestedInput

def secondProfileMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput) (htu : i.u ≤ i.t)
    (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  2 * rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i 0) +
    2 * RationalExpression.metadataAllowance c (RationalNestedParametersCode.scalarPrograms 3) (RationalNestedParametersCode.environment i 0) +
      familyMidpointConstructionMetadataWork primitive c i i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K bits +
        if hTt : i.mirrorLength < i.t then
          rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i 0) +
            RationalExpression.metadataAllowance c (RationalNestedParametersCode.scalarPrograms 4) (RationalNestedParametersCode.environment i 0) +
              secondUniformMetadataWork primitive c i htu hTt +
                RationalSegmentLottery.binaryMetadataWork primitive c i.secondAlpha
                  ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩
                  (i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K bits)
                  (i.secondUniformLottery htu hTt)
        else (i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K bits).paddingMetadataWork primitive 9 0

def secondProfileMetadataBound (c s K : ℕ) : ℕ :=
  3 * rationalEnvironmentMetadataBound c 7 (1 + 2 * s) + 384 * RationalExpression.metadataInstructionBound c 7 128 +
    familyInputMetadataBound c (expressionHeightBudget s 8) + firstMidpointConstructionMetadataBound c (expressionHeightBudget s 16) K +
      secondUniformMetadataBound c s + 18 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 43) +
        72 * RationalExpression.metadataInstructionBound c 2 5 +
          PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 45) +
            PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 43)

theorem secondProfileMetadataBound_mono (c : ℕ) {s t K L : ℕ} (hs : s ≤ t) (hK : K ≤ L) :
    secondProfileMetadataBound c s K ≤ secondProfileMetadataBound c t L := by
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 7) (show 1 + 2 * s ≤ 1 + 2 * t by omega)
  have hFamily := familyInputMetadataBound_mono c (expressionHeightBudget_input_mono hs 8)
  have hMidpoint := firstMidpointConstructionMetadataBound_mono c (expressionHeightBudget_input_mono hs 16) hK
  have hUniform := secondUniformMetadataBound_mono c hs
  have h43 := expressionHeightBudget_input_mono hs 43
  have hAssemblyEnv := rationalEnvironmentMetadataBound_mono c (le_refl 2) (show 1 + 2 * expressionHeightBudget s 43 ≤ 1 + 2 * expressionHeightBudget t 43 by omega)
  have hAssembly := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 18) (expressionHeightBudget_input_mono hs 45)
  have hPadding := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 18) h43
  unfold secondProfileMetadataBound
  gcongr

theorem FieldsHeight.secondProfileMetadataWork_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (htu : i.u ≤ i.t)
    (K : ℕ) (hK : K + 2 ≤ s) (bits : Fin K → Bool) :
    secondProfileMetadataWork primitive c i htu K bits ≤ secondProfileMetadataBound c s K := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _ (fun j => rationalWordWidth_of_height (h.environment 0 hZero j))
  have hMirror := RationalExpression.metadataAllowance_uniform_bound c (RationalNestedParametersCode.scalarPrograms 3)
    (RationalNestedParametersCode.environment i 0) 7 128 le_rfl (RationalNestedParametersCode.scalar_operationBound 3)
  have hMirrorHeight := h.scalar hs 0 hZero 3
  change RationalHeight i.mirrorLength (expressionHeightBudget s 8) at hMirrorHeight
  have hFamily := (h.mono (expressionHeightBudget_ge_input s 8)).familyMidpointConstructionMetadataWork_bound
    (hs.trans (expressionHeightBudget_ge_input s 8)) primitive c hPrimitive i.mirrorLength
    (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 hMirrorHeight K bits
  rw [expressionHeightBudget_comp] at hFamily
  change familyMidpointConstructionMetadataWork primitive c i i.mirrorLength (i.mirrorLength_bounds htu).1
    (i.mirrorLength_bounds htu).2.1 K bits ≤ familyInputMetadataBound c (expressionHeightBudget s 8) +
      firstMidpointConstructionMetadataBound c (expressionHeightBudget s 16) K at hFamily
  let f := i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K bits
  have hF : f.HeightAt (expressionHeightBudget s 43) := h.familyLottery hs i.mirrorLength
    (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 hMirrorHeight K bits hK
  have hs43 := hs.trans (expressionHeightBudget_ge_input s 43)
  unfold secondProfileMetadataWork
  split
  · rename_i hTt
    have hAlpha := RationalExpression.metadataAllowance_uniform_bound c (RationalNestedParametersCode.scalarPrograms 4)
      (RationalNestedParametersCode.environment i 0) 7 128 le_rfl (RationalNestedParametersCode.scalar_operationBound 4)
    have hUniform := h.secondUniformMetadataWork_bound hs primitive c hPrimitive htu hTt
    have hA := h.scalar hs 0 hZero 4
    change RationalHeight i.secondAlpha (expressionHeightBudget s 8) at hA
    have hMix := RationalSegmentLottery.binaryMetadataWork_bound primitive c hPrimitive i.secondAlpha
      ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩ f (i.secondUniformLottery htu hTt) _ hs43
      (hA.mono (expressionHeightBudget_mono s (by decide : 8 ≤ 43))) hF
      ((h.secondUniform hs htu hTt).mono (expressionHeightBudget_mono s (by decide : 28 ≤ 43)))
    rw [expressionHeightBudget_comp] at hMix
    change RationalSegmentLottery.binaryMetadataWork primitive c i.secondAlpha
      ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩
      (i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K bits) (i.secondUniformLottery htu hTt) ≤
        18 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 43) +
          72 * RationalExpression.metadataInstructionBound c 2 5 +
            PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 45) at hMix
    unfold secondProfileMetadataBound
    omega
  · have hPad := RationalSegmentLottery.paddingMetadataWork_bound primitive c hPrimitive f 9 0 _ hs43 hF
    change (i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K bits).paddingMetadataWork primitive 9 0 ≤
      PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 43) at hPad
    unfold secondProfileMetadataBound
    omega

end Blotto.RationalNestedInput
