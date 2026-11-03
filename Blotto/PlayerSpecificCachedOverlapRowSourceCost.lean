import Blotto.PlayerSpecificCachedOverlapRowBounds

/-! Complete cached-row source work, including its single shared
weight/comparison and only the selected endpoint-vector programs. -/
namespace Blotto.PlayerSpecificCachedOverlapRowSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificCachedOverlapRowExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

def weightCoefficient : ℕ := (PlayerSpecificExpressionVectorExecution.operations weightPrograms+16+1+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 7
def firstCoefficient (b : Bool) : ℕ := (PlayerSpecificExpressionVectorExecution.operations (firstPrograms b)+16+4+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 9
def secondCoefficient (b : Bool) : ℕ := (PlayerSpecificExpressionVectorExecution.operations (secondPrograms b)+16+4+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 9
def pointCoefficient : ℕ := firstCoefficient false+firstCoefficient true+secondCoefficient false+secondCoefficient true
def work (H : ℕ) : ℕ := weightCoefficient*(H+28)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+1)^3+
  PlayerSpecificCompareSourceCost.coefficient*(iterate 8 H+1)^3+pointCoefficient*(H+31)^3+
  (5200*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 10 H+21)^3+10
theorem false_profile (A B C D X : ℕ) : A*X+C*X≤(A+B+C+D)*X := by nlinarith only [Nat.zero_le (B*X),Nat.zero_le (D*X)]
theorem true_profile (A B C D X : ℕ) : B*X+D*X≤(A+B+C+D)*X := by nlinarith only [Nat.zero_le (A*X),Nat.zero_le (C*X)]
theorem join {a b c p q f A B C P F : ℕ} (ha : a≤A) (hb : b≤B) (hc : c≤C) (hp : p+q≤P) (hf : f≤F) :
    a+b+c+p+q+f+10≤A+B+C+P+F+10 := by omega

theorem point_cost (root : Candidate) (env : FixedArrayTable 16 Data) (b : Bool) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    (PlayerSpecificExpressionVectorExecution.run RationalCostModel.schoolbook root env (firstPrograms b)).2+
      (PlayerSpecificExpressionVectorExecution.run RationalCostModel.schoolbook root env (secondPrograms b)).2≤pointCoefficient*(H+31)^3 := by
  have hp:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root env (firstPrograms b) H 9 hm hm0 hml hmH he hv hEnv
    (PlayerSpecificCachedOverlapRowPrograms.first_depth b)
    (fun j => ((firstPrograms b).read j).LiteralHeights_mono hH (PlayerSpecificCachedOverlapRowPrograms.first_literals b j))
  have hq:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root env (secondPrograms b) H 9 hm hm0 hml hmH he hv hEnv
    (PlayerSpecificCachedOverlapRowPrograms.second_depth b)
    (fun j => ((secondPrograms b).read j).LiteralHeights_mono hH (PlayerSpecificCachedOverlapRowPrograms.second_literals b j))
  rw [show H+4+16+11=H+31 by omega] at hp hq
  change _≤firstCoefficient b*(H+31)^3 at hp
  change _≤secondCoefficient b*(H+31)^3 at hq
  cases b
  · exact (Nat.add_le_add hp hq).trans (false_profile _ _ _ _ _)
  · exact (Nat.add_le_add hp hq).trans (true_profile _ _ _ _ _)

theorem cost (root : Candidate) (env : FixedArrayTable 16 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    (run RationalCostModel.schoolbook root env).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let weight:=PlayerSpecificAlgebraicExpression.run model root env OverlapFormulaCode.weight
  let zero:=PlayerSpecificAlgebraicField.constant root.polynomial 0
  let b:=PlayerSpecificAlgebraicPairStep.le model root weight zero
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 8 H
  have hstep:=PlayerSpecificAlgebraicExpressionBudget.fuel_mono H (by decide : 1≤8)
  have hw:=PlayerSpecificCachedOverlapRowBounds.weight model root env H hm hm0 hml hmH hH hEnv
  have hz : Reduced root.polynomial zero ∧ HasHeight zero (iterate 8 H) :=
    ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
      mono (constant_height root.polynomial 0 H hmH (zero_height.mono (by omega)) (by omega) hml) hstep⟩
  have hwc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root env weightPrograms H 7 hm hm0 hml hmH he hv hEnv
    PlayerSpecificCachedOverlapRowPrograms.weight_depth
    (fun j => (weightPrograms.read j).LiteralHeights_mono hH (PlayerSpecificCachedOverlapRowPrograms.weight_literals j))
  change _≤weightCoefficient*(H+1+16+11)^3 at hwc
  rw [show H+1+16+11=H+28 by omega] at hwc
  have hzc:=(PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model root 0 H hm hm0 hml hmH (zero_height.mono (by omega))
    (by omega)).trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 H)
  have hc:=PlayerSpecificCompareSourceCost.cost root weight zero (iterate 8 H) hm hm0 hml (mono hmH hbase) (mono he hbase) hv
    ((show 1≤H by omega).trans hbase) hw hz
  have hp:=point_cost root env b H hm hm0 hml hmH he hv hH hEnv
  have hf:=PlayerSpecificCachedOverlapRowBounds.frame_cost root env H hm hm0 hml hmH he hH hEnv
  rw [price_equation]
  exact join hwc hzc hc hp hf

end Blotto.PlayerSpecificCachedOverlapRowSourceCost
