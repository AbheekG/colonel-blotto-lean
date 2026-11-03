import Blotto.GeneralPaperThreeStaticPrograms

/-! Exact formula correspondence for all regular/exceptional and ordered/
swapped cases. Zero-weight slots and their stored endpoints remain covered. -/
namespace Blotto.GeneralPaperThreeStaticPrograms
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem ordered_weight_value (i : RationalThreeSpec) (slot : Fin 9) :
    ((orderedWeight slot).run (RationalThreeSpecCode.environment i)).1 = i.orderedInput.segmentLottery.weight slot := by
  unfold orderedWeight
  simp only [RationalExpression.run, regime_value]
  by_cases hE : 0 < i.orderedInput.a + i.orderedInput.d - i.orderedInput.B
  · rw [ite_eq_right (not_le.mpr hE), GeneralPaperExpressionSubstitution.data, geometry_environment i hE]
    rw [RationalThreeInput.segmentLottery, dite_eq_left hE, RationalThreeGeometryCode.compiledLottery_eq]
    exact RationalThreeGeometryCode.chosen_value _ slot
  · rw [ite_eq_left (le_of_not_gt hE), RationalThreeInput.segmentLottery, dite_eq_right hE]

theorem ordered_left_value (i : RationalThreeSpec) (slot : Fin 9) (j : Fin 3) :
    ((orderedLeft slot j).run (RationalThreeSpecCode.environment i)).1 = i.orderedInput.segmentLottery.P slot j := by
  unfold orderedLeft
  simp only [RationalExpression.run, regime_value]
  by_cases hE : 0 < i.orderedInput.a + i.orderedInput.d - i.orderedInput.B
  · rw [ite_eq_right (not_le.mpr hE), GeneralPaperExpressionSubstitution.data, geometry_environment i hE]
    rw [RationalThreeInput.segmentLottery, dite_eq_left hE, RationalThreeGeometryCode.compiledLottery_eq]
    exact RationalThreeGeometryCode.vertex_value _ _ j
  · rw [ite_eq_left (le_of_not_gt hE), RationalThreeInput.segmentLottery, dite_eq_right hE]
    fin_cases j <;> rfl

theorem ordered_right_value (i : RationalThreeSpec) (slot : Fin 9) (j : Fin 3) :
    ((orderedRight slot j).run (RationalThreeSpecCode.environment i)).1 = i.orderedInput.segmentLottery.Q slot j := by
  unfold orderedRight
  simp only [RationalExpression.run, regime_value]
  by_cases hE : 0 < i.orderedInput.a + i.orderedInput.d - i.orderedInput.B
  · rw [ite_eq_right (not_le.mpr hE), GeneralPaperExpressionSubstitution.data, geometry_environment i hE]
    rw [RationalThreeInput.segmentLottery, dite_eq_left hE, RationalThreeGeometryCode.compiledLottery_eq]
    exact RationalThreeGeometryCode.vertex_value _ _ j
  · rw [ite_eq_left (le_of_not_gt hE), RationalThreeInput.segmentLottery, dite_eq_right hE]
    fin_cases j <;> rfl

theorem weight_value (i : RationalThreeSpec) (slot : Fin 9) :
    ((orderedWeight slot).run (RationalThreeSpecCode.environment i)).1 = i.segmentLottery.weight slot := by
  unfold RationalThreeSpec.segmentLottery
  dsimp only
  split <;> exact ordered_weight_value i slot

theorem left_value (i : RationalThreeSpec) (slot : Fin 9) (j : Fin 3) :
    ((left slot j).run (RationalThreeSpecCode.environment i)).1 = i.segmentLottery.P slot j := by
  unfold left
  have h1 : (RationalThreeSpecCode.environment i).read 1 = i.a := rfl
  have h2 : (RationalThreeSpecCode.environment i).read 2 = i.d := rfl
  simp only [RationalExpression.run, h1, h2]
  unfold RationalThreeSpec.segmentLottery
  by_cases h : i.a ≤ i.d
  · simp only [ite_eq_left h]
    exact ordered_left_value i slot j
  · simp only [ite_eq_right h]
    fin_cases j <;> exact ordered_left_value i slot _

theorem right_value (i : RationalThreeSpec) (slot : Fin 9) (j : Fin 3) :
    ((right slot j).run (RationalThreeSpecCode.environment i)).1 = i.segmentLottery.Q slot j := by
  unfold right
  have h1 : (RationalThreeSpecCode.environment i).read 1 = i.a := rfl
  have h2 : (RationalThreeSpecCode.environment i).read 2 = i.d := rfl
  simp only [RationalExpression.run, h1, h2]
  unfold RationalThreeSpec.segmentLottery
  by_cases h : i.a ≤ i.d
  · simp only [ite_eq_left h]
    exact ordered_right_value i slot j
  · simp only [ite_eq_right h]
    fin_cases j <;> exact ordered_right_value i slot _

end Blotto.GeneralPaperThreeStaticPrograms
