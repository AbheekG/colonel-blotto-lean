import Blotto.RationalNestedResidualCode
import Blotto.RationalNestedProfile

/-! All native ordered nested descriptor branches have word heights linear
in input height plus finite precision. No positivity slack enters the bound. -/

namespace Blotto.RationalNestedInput

theorem FieldsHeight.u {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) :
    RationalHeight i.u (expressionHeightBudget s 1) := by
  rw [show expressionHeightBudget s 1 = s + s + 1 by norm_num [expressionHeightBudget]; omega]
  exact h.1.sub h.2.1

theorem FieldsHeight.v {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) :
    RationalHeight i.v (expressionHeightBudget s 1) := by
  rw [show expressionHeightBudget s 1 = s + s + 1 by norm_num [expressionHeightBudget]; omega]
  exact h.1.sub h.2.2.1

theorem FieldsHeight.h {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s) :
    RationalHeight i.h (expressionHeightBudget s 2) := by
  have hDiff : RationalHeight (i.c - i.t) (expressionHeightBudget s 1) := by
    rw [show expressionHeightBudget s 1 = s + s + 1 by norm_num [expressionHeightBudget]; omega]
    exact h.2.2.2.1.sub h.2.2.2.2.1
  have hQ := h.2.2.2.2.2.mono (expressionHeightBudget_ge_input s 1)
  exact (hQ.mul hDiff).mono (by
    have he : expressionHeightBudget s 2 = 2 * expressionHeightBudget s 1 + 1 := expressionHeightBudget_succ s 1
    omega)

theorem FieldsHeight.residual {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hvt : i.v < i.t) (htu : i.t < i.u) :
    (i.residualInput hvt htu).segmentLottery.HeightAt (expressionHeightBudget s 10) := by
  have hm := expressionHeightBudget_mono s (by decide : 1 ≤ 2)
  have hW : RationalHeight (i.M - i.c) (expressionHeightBudget s 1) := by
    rw [show expressionHeightBudget s 1 = s + s + 1 by norm_num [expressionHeightBudget]; omega]
    exact h.1.sub h.2.2.2.1
  have hT := h.2.2.2.2.1.mono (expressionHeightBudget_ge_input s 2)
  have hEnv : ∀ j, RationalHeight ((RationalNestedResidualCode.environment (i.residualInput hvt htu)).read j)
      (expressionHeightBudget s 2) := by
    intro j
    fin_cases j
    · simpa [RationalNestedResidualCode.environment, FixedArrayTable.read_ofFn, residualInput, geometry] using h.u.mono hm
    · simpa [RationalNestedResidualCode.environment, FixedArrayTable.read_ofFn, residualInput, geometry] using h.v.mono hm
    · simpa [RationalNestedResidualCode.environment, FixedArrayTable.read_ofFn, residualInput, geometry] using hW.mono hm
    · simpa [RationalNestedResidualCode.environment, FixedArrayTable.read_ofFn, residualInput, geometry] using h.h
    · simpa [RationalNestedResidualCode.environment, FixedArrayTable.read_ofFn, residualInput] using hT
  have hTable := RationalNestedResidualCode.descriptor_height _ _
    (hs.trans (expressionHeightBudget_ge_input s 2)) hEnv
  rw [expressionHeightBudget_comp] at hTable
  exact hTable

theorem FieldsHeight.familyLottery {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v)
    (hX : RationalHeight x (expressionHeightBudget s 8)) (K : ℕ) (bits : Fin K → Bool)
    (hK : K + 2 ≤ s) :
    (i.familyLottery x hx0 hxv K bits).HeightAt (expressionHeightBudget s 43) := by
  have hm := expressionHeightBudget_ge_input s 8
  have hFamily := (h.mono hm).familyInput (hs.trans hm) x hx0 hxv hX
  rw [expressionHeightBudget_comp] at hFamily
  have hLevel := expressionHeightBudget_ge_input s 16
  have hTable := hFamily.firstMidpoint (hs.trans hLevel) hxv K bits
  rw [max_eq_left (hK.trans hLevel), expressionHeightBudget_comp] at hTable
  exact hTable

theorem FieldsHeight.secondUniform {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    (i.secondUniformLottery htu hTt).HeightAt (expressionHeightBudget s 28) := by
  have h0 : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hMirror : RationalHeight i.mirrorLength (expressionHeightBudget s 8) := h.scalar hs 0 h0 3
  have hm := expressionHeightBudget_ge_input s 8
  have hB := (h.1.mono hm).sub hMirror
  have hC := (h.2.2.2.2.1.mono hm).sub hMirror
  have he : expressionHeightBudget s 9 = expressionHeightBudget s 8 + expressionHeightBudget s 8 + 1 := by
    rw [show 9 = 8 + 1 by decide, expressionHeightBudget_succ]; omega
  rw [← he] at hB hC
  have hm9 := expressionHeightBudget_ge_input s 9
  have hOne : RationalHeight (1 : ℚ) (expressionHeightBudget s 9) :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans hm9)
  have hEnv : ∀ j, RationalHeight ((RationalThreeInputCode.environment (i.secondUniformInput htu hTt)).read j)
      (expressionHeightBudget s 9) := by
    intro j
    fin_cases j
    · simpa [RationalThreeInputCode.environment, FixedArrayTable.read_ofFn, secondUniformInput] using hB
    · simpa [RationalThreeInputCode.environment, FixedArrayTable.read_ofFn, secondUniformInput] using h.2.1.mono hm9
    · simpa [RationalThreeInputCode.environment, FixedArrayTable.read_ofFn, secondUniformInput] using h.2.2.1.mono hm9
    · simpa [RationalThreeInputCode.environment, FixedArrayTable.read_ofFn, secondUniformInput] using hC
    · simpa [RationalThreeInputCode.environment, FixedArrayTable.read_ofFn, secondUniformInput] using hOne
  have hBase : (i.secondUniformInput htu hTt).segmentLottery.HeightAt (expressionHeightBudget s 27) := by
    constructor
    · intro slot
      have hw := RationalThreeInputCode.segment_weight_height _ slot _ (hs.trans hm9) hEnv
      rw [expressionHeightBudget_comp] at hw
      exact hw
    · intro slot j
      have hend := RationalThreeInputCode.segment_endpoint_heights _ slot j _ (hs.trans hm9) hEnv
      rw [expressionHeightBudget_comp] at hend
      have hm13 := expressionHeightBudget_mono s (by decide : 13 ≤ 27)
      exact ⟨hend.1.mono hm13, hend.2.mono hm13⟩
  have hShift := hBase.shiftThird i.mirrorLength (hMirror.mono (expressionHeightBudget_mono s (by decide : 8 ≤ 27)))
  rw [expressionHeightBudget_comp] at hShift
  exact hShift

theorem FieldsHeight.secondProfile {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (htu : i.u ≤ i.t) (K : ℕ) (bits : Fin K → Bool) (hK : K + 2 ≤ s) :
    (i.secondProfile htu K bits).HeightAt (expressionHeightBudget s 45) := by
  have h0 : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hMirror : RationalHeight i.mirrorLength (expressionHeightBudget s 8) := h.scalar hs 0 h0 3
  have hFamily := h.familyLottery hs i.mirrorLength (i.mirrorLength_bounds htu).1
    (i.mirrorLength_bounds htu).2.1 hMirror K bits hK
  have hs43 := hs.trans (expressionHeightBudget_ge_input s 43)
  unfold RationalNestedInput.secondProfile
  dsimp only
  split
  · rename_i hTt
    have hUniform := (h.secondUniform hs htu hTt).mono (expressionHeightBudget_mono s (by decide : 28 ≤ 43))
    have hAlpha : RationalHeight i.secondAlpha (expressionHeightBudget s 43) :=
      (h.scalar hs 0 h0 4).mono (expressionHeightBudget_mono s (by decide : 8 ≤ 43))
    have hMix := hFamily.binary hUniform hs43 i.secondAlpha
      ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩ hAlpha
    rw [expressionHeightBudget_comp] at hMix
    exact hMix
  · exact (hFamily.padRight hs43 9 0).mono (expressionHeightBudget_mono s (by decide : 43 ≤ 45))

theorem FieldsHeight.thirdProfile {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) (bits : Fin K → Bool) (hK : K + 2 ≤ s) :
    (i.thirdProfile hvt htu K bits).HeightAt (expressionHeightBudget s 45) := by
  have hs10 := hs.trans (expressionHeightBudget_ge_input s 10)
  have hResidual := (h.residual hs hvt htu).padRight hs10 6 0
  have h0 : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hs43 := hs.trans (expressionHeightBudget_ge_input s 43)
  unfold RationalNestedInput.thirdProfile
  dsimp only
  split
  · rename_i hv
    have hV := h.v.mono (expressionHeightBudget_mono s (by decide : 1 ≤ 8))
    have hFamily := h.familyLottery hs i.v hv le_rfl hV K bits hK
    have hAlpha : RationalHeight i.thirdAlpha (expressionHeightBudget s 43) :=
      (h.scalar hs 0 h0 5).mono (expressionHeightBudget_mono s (by decide : 8 ≤ 43))
    have hMix := hFamily.binary (hResidual.mono (expressionHeightBudget_mono s (by decide : 10 ≤ 43))) hs43 i.thirdAlpha
      ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩ hAlpha
    rw [expressionHeightBudget_comp] at hMix
    exact hMix
  · exact (hResidual.padRight hs10 9 0).mono (expressionHeightBudget_mono s (by decide : 10 ≤ 45))

theorem FieldsHeight.profile {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin K → Bool) :
    (i.profile K bits).HeightAt (expressionHeightBudget (max s (K + 2)) 45) := by
  let w := max s (K + 2)
  have hFields := h.mono (le_max_left s (K + 2))
  have hw : 2 ≤ w := hs.trans (le_max_left _ _)
  have hK : K + 2 ≤ w := le_max_right _ _
  unfold RationalNestedInput.profile
  split
  · rename_i htv
    have hFirst := hFields.firstMidpoint hw htv K bits
    rw [max_eq_left hK] at hFirst
    exact (hFirst.padRight (hw.trans (expressionHeightBudget_ge_input w 27)) 9 0).mono
      (expressionHeightBudget_mono w (by decide : 27 ≤ 45))
  · split
    · exact hFields.secondProfile hw _ K bits hK
    · exact hFields.thirdProfile hw _ _ K bits hK

end Blotto.RationalNestedInput
