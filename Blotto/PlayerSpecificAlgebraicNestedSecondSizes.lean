import Blotto.PlayerSpecificAlgebraicNestedSecondReference

/-! The second uniform descriptor uses a fixed number of height layers,
including its raw budget subtraction and the final third-coordinate shift. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSecondSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicNestedSecondUniform
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem input_bounds (root : Candidate) (a : Input) (p : Prepared) (T : ℕ) (ha : Fits root a T)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 1 ≤ T) :
    PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root (input root a p) (step T) := by
  have hbase : T ≤ step T := (Nat.le_succ _).trans (large T)
  have hshort : T+T+1 ≤ step T := by
    have h := calibrate 3 T (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  refine ⟨?_,⟨ha.first.1,mono ha.first.2 hbase⟩,⟨ha.second.1,mono ha.second.2 hbase⟩,?_,?_⟩
  · exact ⟨PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0,
      mono (PlayerSpecificShortReduction.minus_height _ _ _ hm hm0 ha.budget.1 hp.mirror.1 T T ha.budget.2 hp.mirror.2) hshort⟩
  · exact ⟨PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0,
      mono (PlayerSpecificShortReduction.minus_height _ _ _ hm hm0 ha.short.1 hp.mirror.1 T T ha.short.2 hp.mirror.2) hshort⟩
  · exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
      constant_height root.polynomial 1 T hmT (one_height.mono hT) hT hml⟩

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (T : ℕ)
    (ha : Fits root a T) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    PlayerSpecificAlgebraicDescriptorBounds.Bounds root (prepare model root a p) (iterate 22 T) := by
  have hstep := PlayerSpecificAlgebraicExpressionBudget.initial_le 1 T
  have hi := input_bounds root a p T ha hp hm hm0 hml hmT (by omega)
  have hd := PlayerSpecificAlgebraicThreeDescriptorSizes.ordered model root (input root a p) (step T) hi hm hm0 hml
    (mono hmT hstep) (hT.trans hstep)
  change PlayerSpecificAlgebraicDescriptorBounds.Bounds root
    (PlayerSpecificAlgebraicOrderedThree.prepare model root (input root a p)) (iterate 20 (iterate 1 T)) at hd
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hd
  have h21 := PlayerSpecificAlgebraicExpressionBudget.initial_le 21 T
  exact PlayerSpecificAlgebraicDescriptorShift.bounds root p.mirror _ (iterate 21 T) hm hm0
    ⟨hp.mirror.1,mono hp.mirror.2 h21⟩ hd

end Blotto.PlayerSpecificAlgebraicNestedSecondSizes
