import Blotto.PlayerSpecificAlgebraicNestedInteriorProfile

/-! The actual three-way dispatcher and its cached parameter preparation
have one fixed-depth bound, with no dependence on the sampled coin values. -/
namespace Blotto.PlayerSpecificAlgebraicNestedInteriorSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificSegmentAssemblyProperties
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (T K : ℕ) : ℕ := PlayerSpecificAlgebraicNestedRemainingSizes.height (iterate 9 T) K

theorem selected (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (T : ℕ)
    (ha : Fits root a T) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (K : ℕ) (outer : Fin K → Bool) :
    Bounds root (PlayerSpecificAlgebraicNestedInteriorProfile.selected model root a p K outer)
      (PlayerSpecificAlgebraicNestedRemainingSizes.height T K) := by
  unfold PlayerSpecificAlgebraicNestedInteriorProfile.selected
  split
  · have hb := PlayerSpecificAlgebraicNestedFirstDrawSizes.table_bounds model root a T ha hm hm0 hml hmT hT K outer
    have hpadded := PlayerSpecificAlgebraicDescriptorPad.bounds root _ 9 0 _ hm0 hb
    apply bounds_mono root _ _ _ hpadded
    have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 9 T
    have hbase : PlayerSpecificAlgebraicNestedFirstDrawSizes.base T K ≤ PlayerSpecificAlgebraicNestedRemainingSizes.base T K := by
      unfold PlayerSpecificAlgebraicNestedFirstDrawSizes.base PlayerSpecificAlgebraicNestedRemainingSizes.base
      omega
    exact (PlayerSpecificAlgebraicNestedRemainingSizes.iterate_mono 32 hbase).trans
      (PlayerSpecificAlgebraicExpressionBudget.fuel_mono _ (by omega : 32 ≤ 35))
  · split
    · exact PlayerSpecificAlgebraicNestedRemainingSizes.second model root a p T ha hp hm hm0 hml hmT hT K outer
    · exact PlayerSpecificAlgebraicNestedRemainingSizes.third model root a p T ha hp hm hm0 hml hmT hT K outer

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (K : ℕ) (outer : Fin K → Bool) :
    Bounds root (PlayerSpecificAlgebraicNestedInteriorProfile.prepare model root a K outer) (height T K) := by
  have hp := PlayerSpecificAlgebraicNestedCaseParameters.bounds model root a T ha hm hm0 hml hmT hT
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 9 T
  exact selected model root a (PlayerSpecificAlgebraicNestedCaseParameters.prepare model root a) (iterate 9 T)
    (PlayerSpecificAlgebraicNestedInputTools.fits_mono root a T _ ha hi) hp hm hm0 hml (mono hmT hi) (hT.trans hi) K outer

theorem input_le (T K : ℕ) : T ≤ height T K :=
  (PlayerSpecificAlgebraicExpressionBudget.initial_le 9 T).trans
    ((PlayerSpecificAlgebraicNestedRemainingSizes.input_le _ K).trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 35 _))

end Blotto.PlayerSpecificAlgebraicNestedInteriorSizes
