import Blotto.RationalSecondProfileMetadata
import Blotto.RationalResidualInputMetadata
import Blotto.RationalNestedPreparationGuards

/-! Third-profile residual construction is retained before the length guard.
Positive length adds the fixed-mean family/mixture; zero length pads the residual.
The common envelope keeps both possible construction components conservatively. -/

namespace Blotto.RationalNestedInput

def thirdProfileMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  paddedResidualMetadataWork primitive c i hvt htu + rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i 0) +
    RationalExpression.metadataAllowance c (lengthFieldProgram true) (RationalNestedParametersCode.environment i 0) +
      if hv : 0 < i.v then
        2 * rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i 0) +
          RationalExpression.metadataAllowance c (lengthFieldProgram true) (RationalNestedParametersCode.environment i 0) +
            familyMidpointConstructionMetadataWork primitive c i i.v hv le_rfl K bits +
              RationalExpression.metadataAllowance c (RationalNestedParametersCode.scalarPrograms 5) (RationalNestedParametersCode.environment i 0) +
                RationalSegmentLottery.binaryMetadataWork primitive c i.thirdAlpha
                  ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
                  (i.familyLottery i.v hv le_rfl K bits) ((i.residualInput hvt htu).segmentLottery.padRight 6 0)
      else ((i.residualInput hvt htu).segmentLottery.padRight 6 0).paddingMetadataWork primitive 9 0

def thirdProfileMetadataBound (c s K : ℕ) : ℕ :=
  paddedResidualMetadataBound c s + 3 * rationalEnvironmentMetadataBound c 7 (1 + 2 * s) +
    6 * RationalExpression.metadataInstructionBound c 7 3 + 128 * RationalExpression.metadataInstructionBound c 7 128 +
      familyInputMetadataBound c (expressionHeightBudget s 8) + firstMidpointConstructionMetadataBound c (expressionHeightBudget s 16) K +
        18 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 43) +
          72 * RationalExpression.metadataInstructionBound c 2 5 +
            PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 45) +
              PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 10)

theorem thirdProfileMetadataBound_mono (c : ℕ) {s t K L : ℕ} (hs : s ≤ t) (hK : K ≤ L) :
    thirdProfileMetadataBound c s K ≤ thirdProfileMetadataBound c t L := by
  have hResidual := paddedResidualMetadataBound_mono c hs
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 7) (show 1 + 2 * s ≤ 1 + 2 * t by omega)
  have hFamily := familyInputMetadataBound_mono c (expressionHeightBudget_input_mono hs 8)
  have hMidpoint := firstMidpointConstructionMetadataBound_mono c (expressionHeightBudget_input_mono hs 16) hK
  have h43 := expressionHeightBudget_input_mono hs 43
  have hAssemblyEnv := rationalEnvironmentMetadataBound_mono c (le_refl 2) (show 1 + 2 * expressionHeightBudget s 43 ≤ 1 + 2 * expressionHeightBudget t 43 by omega)
  have hAssembly := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 18) (expressionHeightBudget_input_mono hs 45)
  have hPadding := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 18) (expressionHeightBudget_input_mono hs 10)
  unfold thirdProfileMetadataBound
  gcongr

theorem FieldsHeight.thirdProfileMetadataWork_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (hvt : i.v < i.t) (htu : i.t < i.u)
    (K : ℕ) (hK : K + 2 ≤ s) (bits : Fin K → Bool) :
    thirdProfileMetadataWork primitive c i hvt htu K bits ≤ thirdProfileMetadataBound c s K := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _ (fun j => rationalWordWidth_of_height (h.environment 0 hZero j))
  have hLength := RationalExpression.metadataAllowance_uniform_bound c (lengthFieldProgram true)
    (RationalNestedParametersCode.environment i 0) 7 3 le_rfl (by decide)
  have hResidual := h.paddedResidualMetadataWork_bound hs primitive c hPrimitive hvt htu
  let r := (i.residualInput hvt htu).segmentLottery.padRight 6 0
  have hs10 := hs.trans (expressionHeightBudget_ge_input s 10)
  have hR : r.HeightAt (expressionHeightBudget s 10) := (h.residual hs hvt htu).padRight hs10 6 0
  unfold thirdProfileMetadataWork
  split
  · rename_i hv
    have hAlpha := RationalExpression.metadataAllowance_uniform_bound c (RationalNestedParametersCode.scalarPrograms 5)
      (RationalNestedParametersCode.environment i 0) 7 128 le_rfl (RationalNestedParametersCode.scalar_operationBound 5)
    have hV := h.v.mono (expressionHeightBudget_mono s (by decide : 1 ≤ 8))
    have hFamily := (h.mono (expressionHeightBudget_ge_input s 8)).familyMidpointConstructionMetadataWork_bound
      (hs.trans (expressionHeightBudget_ge_input s 8)) primitive c hPrimitive i.v hv le_rfl hV K bits
    rw [expressionHeightBudget_comp] at hFamily
    change familyMidpointConstructionMetadataWork primitive c i i.v hv le_rfl K bits ≤
      familyInputMetadataBound c (expressionHeightBudget s 8) + firstMidpointConstructionMetadataBound c (expressionHeightBudget s 16) K at hFamily
    have hF := h.familyLottery hs i.v hv le_rfl hV K bits hK
    have hA := h.scalar hs 0 hZero 5
    change RationalHeight i.thirdAlpha (expressionHeightBudget s 8) at hA
    have hs43 := hs.trans (expressionHeightBudget_ge_input s 43)
    have hMix := RationalSegmentLottery.binaryMetadataWork_bound primitive c hPrimitive i.thirdAlpha
      ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩ (i.familyLottery i.v hv le_rfl K bits) r _ hs43
      (hA.mono (expressionHeightBudget_mono s (by decide : 8 ≤ 43))) hF
      (hR.mono (expressionHeightBudget_mono s (by decide : 10 ≤ 43)))
    rw [expressionHeightBudget_comp] at hMix
    change RationalSegmentLottery.binaryMetadataWork primitive c i.thirdAlpha
      ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
      (i.familyLottery i.v hv le_rfl K bits) ((i.residualInput hvt htu).segmentLottery.padRight 6 0) ≤
        18 * rationalEnvironmentMetadataBound c 2 (1 + 2 * expressionHeightBudget s 43) +
          72 * RationalExpression.metadataInstructionBound c 2 5 +
            PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 45) at hMix
    unfold thirdProfileMetadataBound
    omega
  · have hPad := RationalSegmentLottery.paddingMetadataWork_bound primitive c hPrimitive r 9 0 _ hs10 hR
    change ((i.residualInput hvt htu).segmentLottery.padRight 6 0).paddingMetadataWork primitive 9 0 ≤
      PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 10) at hPad
    unfold thirdProfileMetadataBound
    omega

end Blotto.RationalNestedInput
