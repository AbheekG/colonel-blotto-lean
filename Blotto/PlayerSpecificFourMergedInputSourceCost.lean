import Blotto.PlayerSpecificFourMergedInputFrameCost

/-! Complete scaled/merged construction prices every actual cached
operation from original raw height, with no parameter/size/cost oracle. -/
namespace Blotto.PlayerSpecificFourMergedInputSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificFourParameterSourceCost.coefficient*(H+25)^3+
  PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3+
  PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3+
  PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 14 H+1)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+1)^3+
  (2800*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 15 H+11)^3+24

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificFourMergedInputExecution.run RationalCostModel.schoolbook root a).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let scale:=(parameters model root a).read 5
  have h13:=PlayerSpecificAlgebraicExpressionBudget.initial_le 13 H
  have h14:=PlayerSpecificAlgebraicExpressionBudget.initial_le 14 H
  have hp:=parameter_bounds model root a H ha hm hm0 hml hmH hH 5
  have hscale : ∀ z,Reduced root.polynomial z ∧ HasHeight z H →
      (PlayerSpecificMixtureScalarExecution.scale model root scale z).2≤PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 13 H+14)^3 := by
    intro z hz
    exact PlayerSpecificMixtureScalarSourceCost.scale_cost root scale z (iterate 13 H) hm hm0 hml (mono hmH h13) (mono he h13) hv
      hp ⟨hz.1,mono hz.2 h13⟩
  have hscaled : ∀ z,Reduced root.polynomial z ∧ HasHeight z H →
      Reduced root.polynomial (PlayerSpecificAlgebraicField.times root.polynomial scale z) ∧
        HasHeight (PlayerSpecificAlgebraicField.times root.polynomial scale z) (iterate 14 H) := by
    intro z hz
    exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
      times_height root.polynomial scale z (iterate 13 H) hm hm0 hml hp.1 hz.1 (mono hmH h13) hp.2 (mono hz.2 h13)⟩
  have hs1:=hscaled a.first ha.first
  have hs2:=hscaled a.second ha.second
  have hmerged:=(PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .add
    (PlayerSpecificAlgebraicField.times root.polynomial scale a.first) (PlayerSpecificAlgebraicField.times root.polynomial scale a.second)
    (iterate 14 H) hm hm0 hml
    hs1.1 hs2.1 (mono hmH h14) hs1.2 hs2.2 ((show 1≤H by omega).trans h14)).trans
      (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 (iterate 14 H))
  simp only [PlayerSpecificAlgebraicExpressionExecution.binary] at hmerged
  have hone:=(PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model root 1 H hm hm0 hml hmH (one_height.mono (by omega)) (by omega)).trans
    (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 H)
  have hpc:=PlayerSpecificFourParameterSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hf:=PlayerSpecificFourMergedInputFrameCost.cost root a H hm hm0 hml hmH he hH ha
  rw [PlayerSpecificFourMergedInputExecution.price_equation]
  unfold work
  refine Nat.add_le_add_right ?_ 24
  refine Nat.add_le_add ?_ hf
  refine Nat.add_le_add ?_ hone
  refine Nat.add_le_add ?_ hmerged
  refine Nat.add_le_add ?_ (hscale a.third ha.third)
  refine Nat.add_le_add ?_ (hscale a.second ha.second)
  exact Nat.add_le_add hpc (hscale a.first ha.first)

end Blotto.PlayerSpecificFourMergedInputSourceCost
