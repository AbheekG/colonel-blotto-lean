import Blotto.RationalFourParametersCode
import Blotto.RationalOverlapHeight
import Blotto.RationalFourGluingDescriptor
import Blotto.RationalNestedSpecHeight
import Blotto.RationalCategoricalHeight

/-! Native four-variable gluing sizes include its auxiliary inputs, both
source couplers, every overlap slot and every dyadic output coordinate. -/

namespace Blotto.RationalFourInput

def FieldsHeight (i : RationalFourInput) (s : ℕ) : Prop :=
  RationalHeight i.B s ∧ RationalHeight i.u s ∧ RationalHeight i.v s ∧
    RationalHeight i.w s ∧ RationalHeight i.ell s ∧ RationalHeight i.p s

theorem FieldsHeight.mono {i : RationalFourInput} {s t : ℕ} (h : i.FieldsHeight s)
    (hst : s ≤ t) : i.FieldsHeight t :=
  ⟨h.1.mono hst, h.2.1.mono hst, h.2.2.1.mono hst,
    h.2.2.2.1.mono hst, h.2.2.2.2.1.mono hst, h.2.2.2.2.2.mono hst⟩

theorem FieldsHeight.environment {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) :
    ∀ j, RationalHeight ((RationalFourParametersCode.environment i).read j) s := by
  intro j
  fin_cases j
  · simpa [RationalFourParametersCode.environment, FixedArrayTable.read_ofFn] using h.1
  · simpa [RationalFourParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.1
  · simpa [RationalFourParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.2.1
  · simpa [RationalFourParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.2.2.1
  · simpa [RationalFourParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.2.2.2.1
  · simpa [RationalFourParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.2.2.2.2

theorem FieldsHeight.scalar {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) (j : Fin 8) :
    RationalHeight (RationalFourParametersCode.values i j) (expressionHeightBudget s 12) :=
  RationalFourParametersCode.height i j s hs h.environment

theorem FieldsHeight.gluingFirst_environment {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    ∀ j, RationalHeight ((RationalThreeSpecCode.environment (i.gluingFirstSpec hcase)).read j)
      (expressionHeightBudget s 12) := by
  rw [i.gluingFirstSpec_refines]
  have hBudget : RationalHeight i.firstBudget (expressionHeightBudget s 12) := h.scalar hs 2
  have hAux : RationalHeight i.auxLength (expressionHeightBudget s 12) := h.scalar hs 1
  have hm := expressionHeightBudget_ge_input s 12
  have hOne : RationalHeight (1 : ℚ) (expressionHeightBudget s 12) :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans hm)
  intro j
  fin_cases j
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingFirstSpecReference] using hBudget
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingFirstSpecReference] using h.2.1.mono hm
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingFirstSpecReference] using h.2.2.1.mono hm
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingFirstSpecReference] using hAux
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingFirstSpecReference] using hOne

theorem FieldsHeight.gluingSecond_environment {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    ∀ j, RationalHeight ((RationalThreeSpecCode.environment (i.gluingSecondSpec hcase)).read j)
      (expressionHeightBudget s 12) := by
  rw [i.gluingSecondSpec_refines]
  have hBudget : RationalHeight i.secondBudget (expressionHeightBudget s 12) := h.scalar hs 3
  have hAux : RationalHeight i.auxLength (expressionHeightBudget s 12) := h.scalar hs 1
  have hm := expressionHeightBudget_ge_input s 12
  intro j
  fin_cases j
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingSecondSpecReference] using hBudget
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingSecondSpecReference] using hAux
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingSecondSpecReference] using h.2.2.2.1.mono hm
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingSecondSpecReference] using h.2.2.2.2.1.mono hm
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, gluingSecondSpecReference] using h.2.2.2.2.2.mono hm

theorem FieldsHeight.gluingDescriptor {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.gluingDescriptor hcase).HeightAt (expressionHeightBudget s 36) := by
  rw [i.gluingDescriptor_refines]
  have hs12 := hs.trans (expressionHeightBudget_ge_input s 12)
  have hFirst := RationalThreeSpecCode.descriptor_height _ _ hs12 (h.gluingFirst_environment hs hcase)
  have hSecond := RationalThreeSpecCode.descriptor_height _ _ hs12 (h.gluingSecond_environment hs hcase)
  rw [expressionHeightBudget_comp] at hFirst hSecond
  have hs30 := hs.trans (expressionHeightBudget_ge_input s 30)
  have hD : RationalHeight i.auxLength (expressionHeightBudget s 30) :=
    (h.scalar hs 1).mono (expressionHeightBudget_mono s (by decide : 12 ≤ 30))
  have hB := h.1.mono (expressionHeightBudget_ge_input s 30)
  have hTable := RationalOverlapGluing.descriptor_height (i.overlapData hcase) i.B _ hs30 hFirst hSecond hD hB
  rw [expressionHeightBudget_comp] at hTable
  exact hTable

theorem FieldsHeight.gluingPoint {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ) (bits : Fin K → Bool) (slot : Fin 81) (j : Fin 4) :
    RationalHeight ((i.gluingDescriptor hcase).point K slot bits j)
      (expressionHeightBudget (max s (K + 2)) 39) := by
  have hFields := h.mono (le_max_left s (K + 2))
  have hm := expressionHeightBudget_ge_input (max s (K + 2)) 36
  have hs36 := hs.trans ((le_max_left s (K + 2)).trans hm)
  have hPoint := (hFields.gluingDescriptor (hs.trans (le_max_left _ _)) hcase).point hs36 K slot bits j
  rw [max_eq_left ((le_max_right s (K + 2)).trans hm), expressionHeightBudget_comp] at hPoint
  exact hPoint

theorem FieldsHeight.gluingPoint_wordWidth {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ) (bits : Fin K → Bool) (slot : Fin 81) (j : Fin 4) :
    rationalWordWidth ((i.gluingDescriptor hcase).point K slot bits j) ≤
      1 + 2 * expressionHeightBudget (max s (K + 2)) 39 :=
  rationalWordWidth_of_height (h.gluingPoint hs hcase K bits slot j)

theorem FieldsHeight.gluingChoice_wordsHeight {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : (1 - i.p) * i.ell ≤ i.w) (fallback : Fin 81) :
    ((categoricalMachine fallback).specification (i.gluingDescriptor hcase).start).WordsHeight
      ((expressionHeightBudget s 36 + 1) * 82) :=
  (h.gluingDescriptor hs hcase).choice_wordsHeight fallback

end Blotto.RationalFourInput
