import Blotto.PlayerSpecificAlgebraicOverlapTable

/-! Computed four-variable parameters and both auxiliary three-core
descriptors retain fixed-depth coefficient bounds. -/
namespace Blotto.PlayerSpecificAlgebraicFourGluingSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicFourGluingInputs PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem first_fits (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root (first root a (parameters model root a)) (iterate 13 T) := by
  have hp := parameter_bounds model root a T ha hm hm0 hml hmT hT
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 13 T
  refine ⟨hp 2,⟨ha.first.1,mono ha.first.2 hi⟩,⟨ha.second.1,mono ha.second.2 hi⟩,hp 1,?_⟩
  exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
    mono (constant_height root.polynomial 1 T hmT (one_height.mono (by omega)) (by omega) hml)
      (PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 1 ≤ 13))⟩

theorem second_fits (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root (second a (parameters model root a)) (iterate 13 T) := by
  have hp := parameter_bounds model root a T ha hm hm0 hml hmT hT
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 13 T
  exact ⟨hp 3,hp 1,⟨ha.third.1,mono ha.third.2 hi⟩,⟨ha.length.1,mono ha.length.2 hi⟩,
    ⟨ha.probability.1,mono ha.probability.2 hi⟩⟩

theorem parents (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    Bounds root (PlayerSpecificAlgebraicUnorderedThree.prepare model root (first root a (parameters model root a))) (iterate 33 T) ∧
      Bounds root (PlayerSpecificAlgebraicUnorderedThree.prepare model root (second a (parameters model root a))) (iterate 33 T) := by
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 13 T
  have hfirst := PlayerSpecificAlgebraicThreeDescriptorSizes.unordered model root _ (iterate 13 T)
    (first_fits model root a T ha hm hm0 hml hmT hT) hm hm0 hml (mono hmT hi) (hT.trans hi)
  have hsecond := PlayerSpecificAlgebraicThreeDescriptorSizes.unordered model root _ (iterate 13 T)
    (second_fits model root a T ha hm hm0 hml hmT hT) hm hm0 hml (mono hmT hi) (hT.trans hi)
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hfirst hsecond
  exact ⟨hfirst,hsecond⟩

end Blotto.PlayerSpecificAlgebraicFourGluingSizes
