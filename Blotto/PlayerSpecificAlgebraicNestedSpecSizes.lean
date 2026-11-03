import Blotto.PlayerSpecificAlgebraicNestedSpecProperties

/-! Endpoint and coordinate-order dispatch fit in the same global
coefficient envelope already established for the interior nested draw. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSpecSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificSegmentAssemblyProperties
open PlayerSpecificAlgebraicNestedSpecInput PlayerSpecificAlgebraicNestedSpecProfile
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem endpoint_le (T K : ℕ) : iterate 21 T ≤ PlayerSpecificAlgebraicNestedInteriorSizes.height T K := by
  have hi := (PlayerSpecificAlgebraicExpressionBudget.initial_le 9 T).trans
    (PlayerSpecificAlgebraicNestedRemainingSizes.input_le (iterate 9 T) K)
  exact (PlayerSpecificAlgebraicNestedRemainingSizes.iterate_mono 21 hi).trans
    (PlayerSpecificAlgebraicExpressionBudget.fuel_mono _ (by omega : 21 ≤ 35))

theorem endpoint_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (useShort : Bool) (T : ℕ)
    (ha : Fits root a T) (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (K : ℕ) :
    Bounds root (PlayerSpecificAlgebraicDescriptorPad.pad
      (PlayerSpecificAlgebraicUnorderedThree.prepare model root (endpoint root a useShort)) 9 0)
      (PlayerSpecificAlgebraicNestedInteriorSizes.height T K) := by
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 1 T
  have hf := PlayerSpecificAlgebraicNestedSpecInputSizes.endpoint_fits root a useShort T ha hm hm0 hml hmT (by omega)
  have hb := PlayerSpecificAlgebraicThreeDescriptorSizes.unordered model root (endpoint root a useShort) (step T) hf hm hm0 hml
    (mono hmT hi) (hT.trans hi)
  change Bounds root (PlayerSpecificAlgebraicUnorderedThree.prepare model root (endpoint root a useShort))
    (iterate 20 (iterate 1 T)) at hb
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hb
  exact bounds_mono root _ _ _ (PlayerSpecificAlgebraicDescriptorPad.bounds root _ 9 0 _ hm0 hb) (endpoint_le T K)

theorem interior_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ)
    (ha : Fits root a T) (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (K : ℕ) (outer : Fin K → Bool) :
    Bounds root (PlayerSpecificAlgebraicNestedSpecProfile.interior model root a K outer) (PlayerSpecificAlgebraicNestedInteriorSizes.height T K) := by
  have h := PlayerSpecificAlgebraicNestedInteriorSizes.bounds model root
    (sorted a (PlayerSpecificAlgebraicPairStep.le model root a.first a.second)) T
    (PlayerSpecificAlgebraicNestedSpecInputSizes.sorted_fits root a _ T ha) hm hm0 hml hmT hT K outer
  unfold PlayerSpecificAlgebraicNestedSpecProfile.interior
  dsimp only
  split
  · exact h
  · exact PlayerSpecificAlgebraicDescriptorSwap.bounds root _ _ h

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ)
    (ha : Fits root a T) (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (K : ℕ) (outer : Fin K → Bool) :
    Bounds root (prepare model root a K outer) (PlayerSpecificAlgebraicNestedInteriorSizes.height T K) := by
  unfold prepare
  split
  · exact endpoint_bounds model root a false T ha hm hm0 hml hmT hT K
  · split
    · exact endpoint_bounds model root a true T ha hm hm0 hml hmT hT K
    · exact interior_bounds model root a T ha hm hm0 hml hmT hT K outer

end Blotto.PlayerSpecificAlgebraicNestedSpecSizes
