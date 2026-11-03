import Blotto.PlayerSpecificNestedProfileSourceCost

/-! A common original-row-height source polynomial for actual exact
algebraic comparisons used by conditional dispatchers and sorting. -/
namespace Blotto.PlayerSpecificCompareSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificAlgebraicComparisonExecution.coefficient*PlayerSpecificResourceCostProfile.rationalCoefficient

theorem cost (root : Candidate) (a b : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H)
    (ha : Reduced root.polynomial a ∧ HasHeight a H) (hb : Reduced root.polynomial b ∧ HasHeight b H) :
    (PlayerSpecificAlgebraicComparisonExecution.run RationalCostModel.schoolbook root a b).2≤coefficient*(H+1)^3 :=
  (PlayerSpecificAlgebraicComparisonExecution.cost RationalCostModel.schoolbook root a b H hm hm0 hml hmH he hv ha.2 hb.2
    (by have h:=ha.1.2; omega) (by have h:=hb.1.2; omega) hH).trans
      (PlayerSpecificResourceCostProfile.cubic PlayerSpecificAlgebraicComparisonExecution.coefficient H)

end Blotto.PlayerSpecificCompareSourceCost
