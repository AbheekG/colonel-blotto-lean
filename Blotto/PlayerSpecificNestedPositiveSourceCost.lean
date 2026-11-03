import Blotto.PlayerSpecificNestedPositiveExecution

/-! Complete source price of the actual conditional test, with the
tested scalar height derived from the original nested rows. -/
namespace Blotto.PlayerSpecificNestedPositiveSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificNestedParameterSourceCost.scalarCoefficient*(H+19)^3+
  (PlayerSpecificAlgebraicComparisonExecution.coefficient*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 9 H+11)^3+2

theorem cost (root : Candidate) (a : Input) (extra : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra H) :
    (PlayerSpecificNestedPositiveExecution.run RationalCostModel.schoolbook root a extra).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let scalar:=(PlayerSpecificNestedParameterExecution.scalar model root a extra 1).1
  let S:=iterate 9 H+10
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 9 H
  have hHS : H≤S := by dsimp [S]; omega
  have hs : Reduced root.polynomial scalar ∧ HasHeight scalar (iterate 9 H) := by
    change Reduced root.polynomial (PlayerSpecificNestedParameterExecution.scalar model root a extra 1).1 ∧
      HasHeight (PlayerSpecificNestedParameterExecution.scalar model root a extra 1).1 (iterate 9 H)
    rw [PlayerSpecificNestedParameterExecution.scalar_value]
    exact scalar_bounds model root a extra H ha hExtra hm hm0 hml hmH hH 1
  have hsc:=PlayerSpecificNestedParameterSourceCost.scalar_cost root a extra 1 H hm hm0 hml hmH he hv hH ha hExtra
  have hcmp:=PlayerSpecificAlgebraicComparisonExecution.cost model root scalar [] S hm hm0 hml
    (mono hmH hHS) (mono he hHS) hv (mono hs.2 (by dsimp [S]; omega)) (nil_height _)
    (by have h:=hs.1.2; omega) (by simp) (by dsimp [S]; omega)
  have hcmp':=hcmp.trans (PlayerSpecificResourceCostProfile.cubic PlayerSpecificAlgebraicComparisonExecution.coefficient S)
  rw [show S+1=iterate 9 H+11 by rfl] at hcmp'
  change _+price model [.control 1]≤_
  rw [PlayerSpecificNestedPositiveExecution.packing]
  exact Nat.add_le_add_right (Nat.add_le_add hsc hcmp') 2

end Blotto.PlayerSpecificNestedPositiveSourceCost
