import Blotto.PlayerSpecificSplitFirstTwoSizes

/-! Complete actual proportional split source price, with cached
denominator/fractions/products and all temporary heights derived. -/
namespace Blotto.PlayerSpecificSplitFirstTwoSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+1)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(step H+1)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(step H+1)^3+
  PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 2 H+14)^3+
  PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 2 H+14)^3+
  (2000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 3 H+11)^3+14

theorem cost (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H)
    (ha : Reduced root.polynomial a ∧ HasHeight a H) (hd : Reduced root.polynomial d ∧ HasHeight d H)
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) H) :
    (PlayerSpecificSplitFirstTwoExecution.run RationalCostModel.schoolbook root a d y).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let denom:=PlayerSpecificAlgebraicField.plus root.polynomial a d
  have hbase : H≤step H := (Nat.le_succ _).trans (large H)
  have htwo:=PlayerSpecificAlgebraicExpressionBudget.initial_le 2 H
  have hfracs:=PlayerSpecificSplitFirstTwoSizes.fractions root a d H hm hm0 hml hmH hH ha hd
  have hsum:=(PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .add a d H hm hm0 hml ha.1 hd.1 hmH ha.2 hd.2 hH).trans
    (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 H)
  have hdiv : ∀ z,Reduced root.polynomial z ∧ HasHeight z H →
      (PlayerSpecificFieldDivisionExecution.run model root.polynomial z denom).2≤
        (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(step H+1)^3 := by
    intro z hz
    exact (PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .divide z denom (step H) hm hm0 hml hz.1 hfracs.1.1
      (mono hmH hbase) (mono hz.2 hbase) hfracs.1.2 (hH.trans hbase)).trans
        (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 (step H))
  have hprod : ∀ z,Reduced root.polynomial z ∧ HasHeight z H →
      (PlayerSpecificMixtureScalarExecution.scale model root (PlayerSpecificAlgebraicField.divide root.polynomial z denom) (y.read 0)).2≤
        PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 2 H+14)^3 := by
    intro z hz
    exact PlayerSpecificMixtureScalarSourceCost.scale_cost root _ (y.read 0) (iterate 2 H) hm hm0 hml
      (mono hmH htwo) (mono he htwo) hv (hfracs.2 z hz) ⟨(hy 0).1,mono (hy 0).2 htwo⟩
  have hf:=PlayerSpecificSplitFirstTwoSizes.frame_cost root a d y H hm hm0 hml hmH he hH ha hd hy
  rw [PlayerSpecificSplitFirstTwoExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsum (hdiv a ha))
    (hdiv d hd)) (hprod a ha)) (hprod d hd)) hf) 14

end Blotto.PlayerSpecificSplitFirstTwoSourceCost
