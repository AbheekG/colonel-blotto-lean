import Blotto.PlayerSpecificAlgebraicNestedRemainingProperties

/-! Both remaining profiles have a common fixed-depth coefficient bound.
Cached parameters, family tables and residual rows all enter this bound. -/
namespace Blotto.PlayerSpecificAlgebraicNestedRemainingSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificSegmentAssemblyProperties
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def base (T K : ℕ) : ℕ := iterate 9 T+K+3
def height (T K : ℕ) : ℕ := iterate 35 (base T K)

theorem iterate_mono (k : ℕ) : Monotone (iterate k) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih => exact PlayerSpecificAlgebraicHeightEnvelope.mono.comp ih

theorem input_le (T K : ℕ) : T ≤ base T K :=
  (PlayerSpecificAlgebraicExpressionBudget.initial_le 9 T).trans (by unfold base; omega)

theorem core_le (k T K : ℕ) (hk : k ≤ 32) : iterate k T ≤ iterate 32 (base T K) :=
  (iterate_mono k (input_le T K)).trans (PlayerSpecificAlgebraicExpressionBudget.fuel_mono _ hk)

theorem third (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (T : ℕ)
    (ha : Fits root a T) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (K : ℕ) (outer : Fin K → Bool) :
    Bounds root (PlayerSpecificAlgebraicNestedThirdProfile.prepare model root a p K outer) (height T K) := by
  have hcore : T ≤ iterate 32 (base T K) := (input_le T K).trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 32 _)
  have hr := PlayerSpecificAlgebraicDescriptorPad.bounds root (PlayerSpecificAlgebraicResidualTable.prepare model root a) 6 0
    (iterate 11 T) hm0 (PlayerSpecificAlgebraicResidualTable.bounds model root a T ha hm hm0 hml hmT hT)
  have hr' := bounds_mono root _ _ _ hr (core_le 11 T K (by omega))
  unfold PlayerSpecificAlgebraicNestedThirdProfile.prepare
  split
  · have hf := PlayerSpecificAlgebraicNestedFamily.profile_bounds model root a p.v T ha hp.v hm hm0 hml hmT hT K outer
    have hb := PlayerSpecificAlgebraicDescriptorBinarySizes.bounds root p.thirdAlpha _ _ (iterate 32 (base T K)) hm hm0 hml
      (mono hmT hcore) ((show 1 ≤ T by omega).trans hcore) ⟨hp.thirdAlpha.1,mono hp.thirdAlpha.2 hcore⟩ hf hr'
    rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hb
    exact hb
  · exact bounds_mono root _ _ _ (PlayerSpecificAlgebraicDescriptorPad.bounds root _ 9 0 _ hm0 hr')
      (PlayerSpecificAlgebraicExpressionBudget.fuel_mono _ (by omega : 32 ≤ 35))

theorem second (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (T : ℕ)
    (ha : Fits root a T) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (K : ℕ) (outer : Fin K → Bool) :
    Bounds root (PlayerSpecificAlgebraicNestedSecondProfile.prepare model root a p K outer) (height T K) := by
  have hcore : T ≤ iterate 32 (base T K) := (input_le T K).trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 32 _)
  have hf := PlayerSpecificAlgebraicNestedFamily.profile_bounds model root a p.mirror T ha hp.mirror hm hm0 hml hmT hT K outer
  unfold PlayerSpecificAlgebraicNestedSecondProfile.prepare
  split
  · have hu := PlayerSpecificAlgebraicNestedSecondSizes.bounds model root a p T ha hp hm hm0 hml hmT hT
    have hu' := bounds_mono root _ _ _ hu (core_le 22 T K (by omega))
    have hb := PlayerSpecificAlgebraicDescriptorBinarySizes.bounds root p.secondAlpha _ _ (iterate 32 (base T K)) hm hm0 hml
      (mono hmT hcore) ((show 1 ≤ T by omega).trans hcore) ⟨hp.secondAlpha.1,mono hp.secondAlpha.2 hcore⟩ hf hu'
    rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hb
    exact hb
  · exact bounds_mono root _ _ _ (PlayerSpecificAlgebraicDescriptorPad.bounds root _ 9 0 _ hm0 hf)
      (PlayerSpecificAlgebraicExpressionBudget.fuel_mono _ (by omega : 32 ≤ 35))

end Blotto.PlayerSpecificAlgebraicNestedRemainingSizes
