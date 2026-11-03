import Blotto.PlayerSpecificAlgebraicFourReflectedInput

/-! All reflected-resource original leaves have fifteen fixed height
layers; their nonrepeating resource paths fit within one further layer. -/
namespace Blotto.PlayerSpecificAlgebraicFourReflectedSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicFourReflectedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem original_bounds (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (T : ℕ) (ha : Fits r.root a T) :
    ∀ j,Reduced r.root.polynomial ((original a).read j) ∧ HasHeight ((original a).read j) T := by
  intro j
  fin_cases j <;> simp only [original,FixedArrayTable.read_ofFn]
  · exact ha.first
  · exact ha.second
  · exact ha.third

theorem bounds (model : RationalCostModel) (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (T : ℕ)
    (ha : Fits r.root a T) (hm : Normalized r.root.polynomial) (hm0 : r.root.polynomial ≠ [])
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) :
    (∀ j,Reduced r.root.polynomial ((prepare model r a).long.read j) ∧ HasHeight ((prepare model r a).long.read j) (iterate 15 T)) ∧
      (∀ j,Reduced r.root.polynomial ((prepare model r a).short.read j) ∧ HasHeight ((prepare model r a).short.read j) (iterate 15 T)) ∧
      (∀ j,(Reduced r.root.polynomial ((prepare model r a).resources.rows.read j).length ∧
        HasHeight ((prepare model r a).resources.rows.read j).length (iterate 15 T)) ∧
        (Reduced r.root.polynomial ((prepare model r a).resources.rows.read j).initialA ∧
          HasHeight ((prepare model r a).resources.rows.read j).initialA (iterate 15 T))) ∧
      (Reduced r.root.polynomial (prepare model r a).budget ∧ HasHeight (prepare model r a).budget (iterate 15 T)) := by
  have hp := parameter_bounds model r.root a T ha hm hm0 hml hmT hT
  have hl := original_bounds r a T ha
  have h013 := PlayerSpecificAlgebraicExpressionBudget.initial_le 13 T
  have h015 := PlayerSpecificAlgebraicExpressionBudget.initial_le 15 T
  have h1314 := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 13 ≤ 14)
  have h1415 := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 14 ≤ 15)
  have h1315 := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 13 ≤ 15)
  have hscaled : ∀ (k : Fin 8) j,Reduced r.root.polynomial
      (PlayerSpecificAlgebraicField.times r.root.polynomial ((parameters model r.root a).read k) ((original a).read j)) ∧
      HasHeight (PlayerSpecificAlgebraicField.times r.root.polynomial ((parameters model r.root a).read k) ((original a).read j)) (iterate 14 T) := by
    intro k j
    exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
      times_height r.root.polynomial _ _ (iterate 13 T) hm hm0 hml (hp k).1 (hl j).1
        (mono hmT h013) (hp k).2 (mono (hl j).2 h013)⟩
  refine ⟨fun j => ⟨(hl j).1,mono (hl j).2 h015⟩,?_,?_,⟨(hp 7).1,mono (hp 7).2 h1315⟩⟩
  · intro j
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact ⟨(hscaled 4 j).1,mono (hscaled 4 j).2 h1415⟩
  · intro j
    simp only [prepare,FixedArrayTable.read_ofFn]
    refine ⟨⟨(hscaled 5 j).1,mono (hscaled 5 j).2 h1415⟩,?_⟩
    exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
      times_height r.root.polynomial _ _ (iterate 14 T) hm hm0 hml (hp 6).1 (hscaled 5 j).1
        (mono hmT (h013.trans h1314)) (mono (hp 6).2 h1314) (hscaled 5 j).2⟩

theorem stored_height_le (H : ℕ) : PlayerSpecificAlgebraicLoopHeights.storedHeight 3 H ≤ step H := by
  have h := calibrate 30 H (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
  unfold PlayerSpecificAlgebraicLoopHeights.storedHeight PlayerSpecificAlgebraicLoopHeights.activeHeight
    PlayerSpecificAlgebraicPairHeights.resourceHeight
  omega

end Blotto.PlayerSpecificAlgebraicFourReflectedSizes
