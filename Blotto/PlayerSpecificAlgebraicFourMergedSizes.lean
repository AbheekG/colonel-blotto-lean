import Blotto.PlayerSpecificAlgebraicFourMergedInput

/-! Scaling and merging add only two height layers to the computed
four-variable parameters; the child rows and split lengths share a bound. -/
namespace Blotto.PlayerSpecificAlgebraicFourMergedSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicFourMergedInput
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    (Reduced root.polynomial (prepare model root a).first ∧ HasHeight (prepare model root a).first (iterate 15 T)) ∧
      (Reduced root.polynomial (prepare model root a).second ∧ HasHeight (prepare model root a).second (iterate 15 T)) ∧
      PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root (prepare model root a).child (iterate 15 T) := by
  have hp := parameter_bounds model root a T ha hm hm0 hml hmT hT 5
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 13 T
  have h1415 := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 14 ≤ 15)
  have h015 := PlayerSpecificAlgebraicExpressionBudget.initial_le 15 T
  have hscale : ∀ z,Reduced root.polynomial z → HasHeight z T →
      Reduced root.polynomial (PlayerSpecificAlgebraicField.times root.polynomial ((parameters model root a).read 5) z) ∧
      HasHeight (PlayerSpecificAlgebraicField.times root.polynomial ((parameters model root a).read 5) z) (iterate 14 T) := by
    intro z hz hzh
    exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
      times_height root.polynomial _ z (iterate 13 T) hm hm0 hml hp.1 hz (mono hmT hi) hp.2 (mono hzh hi)⟩
  have hfirst := hscale a.first ha.first.1 ha.first.2
  have hsecond := hscale a.second ha.second.1 ha.second.2
  have hthird := hscale a.third ha.third.1 ha.third.2
  refine ⟨⟨hfirst.1,mono hfirst.2 h1415⟩,⟨hsecond.1,mono hsecond.2 h1415⟩,?_⟩
  refine ⟨⟨ha.budget.1,mono ha.budget.2 h015⟩,?_,⟨hthird.1,mono hthird.2 h1415⟩,
    ⟨ha.length.1,mono ha.length.2 h015⟩,?_⟩
  · exact ⟨PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0,
      (PlayerSpecificAlgebraicExpressionBudget.binary_heights model root _ _ (iterate 14 T) hm hm0 hml
        hfirst.1 hsecond.1 (mono hmT (PlayerSpecificAlgebraicExpressionBudget.initial_le 14 T))
        hfirst.2 hsecond.2 ((show 1 ≤ T by omega).trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 14 T))).1⟩
  · exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
      mono (constant_height root.polynomial 1 T hmT (one_height.mono (by omega)) (by omega) hml)
        (PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 1 ≤ 15))⟩

end Blotto.PlayerSpecificAlgebraicFourMergedSizes
