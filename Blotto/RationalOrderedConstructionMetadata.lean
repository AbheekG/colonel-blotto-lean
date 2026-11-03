import Blotto.RationalThirdProfileMetadata

/-! All ordered interior profile branches retain one construction envelope,
including both available guard environments and the first-case padding. The
actual branch charge is not clipped. Caller/factory multiplicity is separate. -/

namespace Blotto.RationalNestedInput

def profileConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  2 * rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i 0) +
    RationalExpression.metadataAllowance c (lengthFieldProgram true) (RationalNestedParametersCode.environment i 0) +
      RationalExpression.metadataAllowance c (lengthFieldProgram false) (RationalNestedParametersCode.environment i 0) +
        if htv : i.t ≤ i.v then
          firstMidpointConstructionMetadataWork primitive c i htv K bits +
            (i.firstConditionalLottery htv (i.midpointLocation K bits) (i.midpointLocation_bounds K bits)).paddingMetadataWork primitive 9 0
        else if htu : i.u ≤ i.t then secondProfileMetadataWork primitive c i htu K bits
        else thirdProfileMetadataWork primitive c i (lt_of_not_ge htv) (lt_of_not_ge htu) K bits

def profileConstructionMetadataBound (c s K : ℕ) : ℕ :=
  2 * rationalEnvironmentMetadataBound c 7 (1 + 2 * s) + 6 * RationalExpression.metadataInstructionBound c 7 3 +
    firstMidpointConstructionMetadataBound c s K +
      PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 27) +
        secondProfileMetadataBound c s K + thirdProfileMetadataBound c s K

theorem profileConstructionMetadataBound_mono (c : ℕ) {s t K L : ℕ} (hs : s ≤ t) (hK : K ≤ L) :
    profileConstructionMetadataBound c s K ≤ profileConstructionMetadataBound c t L := by
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 7) (show 1 + 2 * s ≤ 1 + 2 * t by omega)
  have hFirst := firstMidpointConstructionMetadataBound_mono c hs hK
  have hPadding := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 18) (expressionHeightBudget_input_mono hs 27)
  have hSecond := secondProfileMetadataBound_mono c hs hK
  have hThird := thirdProfileMetadataBound_mono c hs hK
  unfold profileConstructionMetadataBound
  gcongr

theorem FieldsHeight.profileConstructionMetadataWork_common {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hK : K + 2 ≤ s) (bits : Fin K → Bool) :
    profileConstructionMetadataWork primitive c i K bits ≤ profileConstructionMetadataBound c s K := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _ (fun j => rationalWordWidth_of_height (h.environment 0 hZero j))
  have hGuardV := RationalExpression.metadataAllowance_uniform_bound c (lengthFieldProgram true)
    (RationalNestedParametersCode.environment i 0) 7 3 le_rfl (by decide)
  have hGuardU := RationalExpression.metadataAllowance_uniform_bound c (lengthFieldProgram false)
    (RationalNestedParametersCode.environment i 0) 7 3 le_rfl (by decide)
  unfold profileConstructionMetadataWork
  split
  · rename_i htv
    have hFirst := h.firstMidpointConstructionMetadataWork_bound hs primitive c hPrimitive htv K bits
    have hTable := h.firstMidpoint hs htv K bits
    rw [max_eq_left hK] at hTable
    have hPadding := RationalSegmentLottery.paddingMetadataWork_bound primitive c hPrimitive _ 9 0 _
      (hs.trans (expressionHeightBudget_ge_input s 27)) hTable
    change (i.firstConditionalLottery htv (i.midpointLocation K bits) (i.midpointLocation_bounds K bits)).paddingMetadataWork primitive 9 0 ≤
      PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 27) at hPadding
    unfold profileConstructionMetadataBound
    omega
  · split
    · rename_i htv htu
      have hSecond := h.secondProfileMetadataWork_bound hs primitive c hPrimitive htu K hK bits
      unfold profileConstructionMetadataBound
      omega
    · rename_i htv htu
      have hThird := h.thirdProfileMetadataWork_bound hs primitive c hPrimitive (lt_of_not_ge htv) (lt_of_not_ge htu) K hK bits
      unfold profileConstructionMetadataBound
      omega

theorem FieldsHeight.profileConstructionMetadataWork_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    profileConstructionMetadataWork primitive c i K bits ≤ profileConstructionMetadataBound c (max s (K + 2)) K :=
  (h.mono (le_max_left _ _)).profileConstructionMetadataWork_common (hs.trans (le_max_left _ _))
    primitive c hPrimitive K (le_max_right _ _) bits

end Blotto.RationalNestedInput
