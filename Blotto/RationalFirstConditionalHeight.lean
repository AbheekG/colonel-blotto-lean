import Blotto.RationalNestedParametersBounds
import Blotto.RationalFirstConditional
import Blotto.RationalThreeInputHeight

/-! Actual first-case conditional descriptor words, including zero probability
and the translated third coordinate, inherit the nested input-height bound. -/

namespace Blotto.RationalNestedParametersCode

theorem environment_fields (i : RationalNestedInput) (x : ℚ) (s : ℕ)
    (hEnv : ∀ j, RationalHeight ((environment i x).read j) s) :
    RationalHeight i.M s ∧ RationalHeight i.a s ∧ RationalHeight i.d s ∧
      RationalHeight i.c s ∧ RationalHeight i.t s ∧ RationalHeight i.q s ∧ RationalHeight x s := by
  have h0 := hEnv 0
  have h1 := hEnv 1
  have h2 := hEnv 2
  have h3 := hEnv 3
  have h4 := hEnv 4
  have h5 := hEnv 5
  have h6 := hEnv 6
  simpa [environment, FixedArrayTable.read_ofFn] using And.intro h0 ⟨h1, h2, h3, h4, h5, h6⟩

theorem first_weight_height (i : RationalNestedInput) (htv : i.t ≤ i.v) (x : ℚ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (slot : Fin 9) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i x).read j) s) :
    RationalHeight ((i.firstConditionalLottery htv x hx).weight slot) (expressionHeightBudget s 19) := by
  unfold RationalNestedInput.firstConditionalLottery
  split
  · rename_i hp
    have hG := first_geometry_height i htv x hx hp s hs hEnv
    have hsG : 2 ≤ expressionHeightBudget s 3 := hs.trans (expressionHeightBudget_ge_input s 3)
    have h := RationalThreeGeometryCode.chosen_height (i.firstGeometry htv x hx hp) slot _ hsG hG
    rw [expressionHeightBudget_comp] at h
    exact h
  · change RationalHeight (if slot = 0 then (1 : ℚ) else 0) (expressionHeightBudget s 19)
    have hS : 2 ≤ expressionHeightBudget s 19 := hs.trans (expressionHeightBudget_ge_input s 19)
    by_cases hz : slot = 0
    · rw [ite_eq_left hz]
      exact (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hS
    · rw [ite_eq_right hz]
      exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hS

theorem first_endpoint_heights (i : RationalNestedInput) (htv : i.t ≤ i.v) (x : ℚ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (slot : Fin 9) (j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i x).read j) s) :
    RationalHeight ((i.firstConditionalLottery htv x hx).P slot j) (expressionHeightBudget s 6) ∧
      RationalHeight ((i.firstConditionalLottery htv x hx).Q slot j) (expressionHeightBudget s 6) := by
  have hf := environment_fields i x s hEnv
  have hX := hf.2.2.2.2.2.2
  unfold RationalNestedInput.firstConditionalLottery
  split
  · rename_i hp
    have hG := first_geometry_height i htv x hx hp s hs hEnv
    have hsG : 2 ≤ expressionHeightBudget s 3 := hs.trans (expressionHeightBudget_ge_input s 3)
    have hP := fun j => RationalThreeGeometryCode.vertex_height (i.firstGeometry htv x hx hp)
      (RationalThreeGeometry.edges slot).1 j _ hsG hG
    have hQ := fun j => RationalThreeGeometryCode.vertex_height (i.firstGeometry htv x hx hp)
      (RationalThreeGeometry.edges slot).2 j _ hsG hG
    have hBase : ∀ j, RationalHeight ((i.firstGeometry htv x hx hp).segmentLottery.P slot j) (expressionHeightBudget s 5) ∧
        RationalHeight ((i.firstGeometry htv x hx hp).segmentLottery.Q slot j) (expressionHeightBudget s 5) := by
      intro k
      have hPk := hP k
      have hQk := hQ k
      rw [expressionHeightBudget_comp] at hPk hQk
      exact ⟨hPk, hQk⟩
    have hm : expressionHeightBudget s 5 ≤ expressionHeightBudget s 6 := expressionHeightBudget_mono s (by decide)
    fin_cases j
    · exact ⟨(hBase 0).1.mono hm, (hBase 0).2.mono hm⟩
    · exact ⟨(hBase 1).1.mono hm, (hBase 1).2.mono hm⟩
    · have hxB := hX.mono (expressionHeightBudget_ge_input s 5)
      have hP2 := (hBase 2).1.add hxB
      have hQ2 := (hBase 2).2.add hxB
      rw [show 6 = 5 + 1 by decide, expressionHeightBudget_succ]
      exact ⟨by simpa [RationalSegmentLottery.shiftThird, two_mul] using hP2,
        by simpa [RationalSegmentLottery.shiftThird, two_mul] using hQ2⟩
  · have hm := expressionHeightBudget_ge_input s 6
    have h0 : RationalHeight (0 : ℚ) (expressionHeightBudget s 6) :=
      (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans hm)
    fin_cases j
    · exact ⟨h0, hf.2.1.mono hm⟩
    · exact ⟨hf.2.2.1.mono hm, h0⟩
    · exact ⟨hX.mono hm, hX.mono hm⟩

end Blotto.RationalNestedParametersCode
