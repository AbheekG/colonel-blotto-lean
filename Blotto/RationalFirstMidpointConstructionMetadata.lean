import Blotto.RationalFirstConditionalMetadata
import Blotto.RationalPreparationCommonPrice

/-! First midpoint construction adds its location environment/control and
the subsequent conditional metadata. Midpoint decoding itself already has a
separate global ledger. Fixed-mean family construction retains probability
environment/control and six stored input fields. -/

namespace Blotto.RationalNestedInput

def firstMidpointConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput)
    (htv : i.t ≤ i.v) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i (dyadicMidpointSample K bits)) +
    RationalExpression.metadataAllowance c (RationalNestedParametersCode.scalarPrograms 0)
      (RationalNestedParametersCode.environment i (dyadicMidpointSample K bits)) +
        firstConditionalMetadataWork primitive c i htv (i.midpointLocation K bits) (i.midpointLocation_bounds K bits)

def firstMidpointConstructionMetadataBound (c s K : ℕ) : ℕ :=
  rationalEnvironmentMetadataBound c 7 (1 + 2 * max s (K + 2)) + 128 * RationalExpression.metadataInstructionBound c 7 128 +
    firstConditionalMetadataBound c (expressionHeightBudget (max s (K + 2)) 8)

theorem firstMidpointConstructionMetadataBound_mono (c : ℕ) {s t K L : ℕ} (hs : s ≤ t) (hK : K ≤ L) :
    firstMidpointConstructionMetadataBound c s K ≤ firstMidpointConstructionMetadataBound c t L := by
  have hBase : max s (K + 2) ≤ max t (L + 2) := by omega
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 7) (show 1 + 2 * max s (K + 2) ≤ 1 + 2 * max t (L + 2) by omega)
  have hConditional := firstConditionalMetadataBound_mono c (expressionHeightBudget_input_mono hBase 8)
  unfold firstMidpointConstructionMetadataBound
  gcongr

theorem FieldsHeight.firstMidpointConstructionMetadataWork_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (htv : i.t ≤ i.v) (K : ℕ) (bits : Fin K → Bool) :
    firstMidpointConstructionMetadataWork primitive c i htv K bits ≤ firstMidpointConstructionMetadataBound c s K := by
  let w := max s (K + 2)
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hMid := (dyadicMidpointSample_height K bits).mono (le_max_right s (K + 2))
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (hW.environment _ hMid j))
  have hScalar := RationalExpression.metadataAllowance_uniform_bound c (RationalNestedParametersCode.scalarPrograms 0)
    (RationalNestedParametersCode.environment i (dyadicMidpointSample K bits)) 7 128 le_rfl (RationalNestedParametersCode.scalar_operationBound 0)
  have hLevel := expressionHeightBudget_ge_input w 8
  have hLocation := h.midpointLocation hs K bits
  have hConditional := (hW.mono hLevel).firstConditionalMetadataWork_bound (hw.trans hLevel) primitive c hPrimitive htv
    (i.midpointLocation K bits) (i.midpointLocation_bounds K bits) hLocation
  exact Nat.add_le_add (Nat.add_le_add hEnv hScalar) hConditional

def familyInputMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput)
    (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) : ℕ :=
  rationalEnvironmentMetadataWork primitive (RationalNestedParametersCode.environment i x) +
    RationalExpression.metadataAllowance c (RationalNestedParametersCode.scalarPrograms 2) (RationalNestedParametersCode.environment i x) +
      rationalArrayCopyWork (List.ofFn (i.familyInputFields x hx0 hxv)) 0 + indexedLoopMetadataBitWork primitive 0 6

def familyInputMetadataBound (c s : ℕ) : ℕ :=
  rationalEnvironmentMetadataBound c 7 (1 + 2 * s) + 128 * RationalExpression.metadataInstructionBound c 7 128 +
    72 * (1 + 2 * expressionHeightBudget s 8) + indexedLoopMetadataBound c 6

theorem familyInputMetadataBound_mono (c : ℕ) : Monotone (familyInputMetadataBound c) := by
  intro a b hab
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 7) (show 1 + 2 * a ≤ 1 + 2 * b by omega)
  have hFields := expressionHeightBudget_input_mono hab 8
  unfold familyInputMetadataBound
  gcongr

theorem FieldsHeight.familyInputMetadataWork_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (hX : RationalHeight x s) :
    familyInputMetadataWork primitive c i x hx0 hxv ≤ familyInputMetadataBound c s := by
  have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (h.environment x hX j))
  have hScalar := RationalExpression.metadataAllowance_uniform_bound c (RationalNestedParametersCode.scalarPrograms 2)
    (RationalNestedParametersCode.environment i x) 7 128 le_rfl (RationalNestedParametersCode.scalar_operationBound 2)
  have hCopy := rationalArrayCopyWork_bound (List.ofFn (i.familyInputFields x hx0 hxv)) 0
  have hWords := rationalWordWidth_sum_bound (List.ofFn (i.familyInputFields x hx0 hxv)) (1 + 2 * expressionHeightBudget s 8)
    (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩; exact rationalWordWidth_of_height (h.familyInputFields hs x hx0 hxv hX j))
  simp only [List.length_ofFn, Nat.zero_add] at hCopy hWords
  have hCopyPrice : rationalArrayCopyWork (List.ofFn (i.familyInputFields x hx0 hxv)) 0 ≤ 72 * (1 + 2 * expressionHeightBudget s 8) := by
    have h := hCopy.trans (Nat.mul_le_mul_left 12 hWords)
    nlinarith
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive 6
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hEnv hScalar) hCopyPrice) hLoop

def familyMidpointConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedInput)
    (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  familyInputMetadataWork primitive c i x hx0 hxv +
    firstMidpointConstructionMetadataWork primitive c (i.familyInput x hx0 hxv) hxv K bits

theorem FieldsHeight.familyMidpointConstructionMetadataWork_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (hX : RationalHeight x s) (K : ℕ) (bits : Fin K → Bool) :
    familyMidpointConstructionMetadataWork primitive c i x hx0 hxv K bits ≤ familyInputMetadataBound c s +
      firstMidpointConstructionMetadataBound c (expressionHeightBudget s 8) K :=
  Nat.add_le_add (h.familyInputMetadataWork_bound hs primitive c hPrimitive x hx0 hxv hX)
    ((h.familyInput hs x hx0 hxv hX).firstMidpointConstructionMetadataWork_bound
      (hs.trans (expressionHeightBudget_ge_input s 8)) primitive c hPrimitive hxv K bits)

end Blotto.RationalNestedInput
