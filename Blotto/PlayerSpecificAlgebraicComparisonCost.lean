import Blotto.PlayerSpecificAlgebraicPairCost

/-! Explicit polynomial prices for the actual comparison and short-circuit
active callers, including all backend and enclosing source work. -/
namespace Blotto.PlayerSpecificAlgebraicComparisonCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def widthCoefficient : ℕ := 2*PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient
def comparisonCoefficient : ℕ := PlayerSpecificAlgebraicComparisonExecution.coefficient*(widthCoefficient^2+widthCoefficient)
def activeCoefficient : ℕ := (2*PlayerSpecificAlgebraicComparisonExecution.coefficient+3)*(widthCoefficient^2+widthCoefficient)

theorem width_linear (H : ℕ) : PlayerSpecificAlgebraicComparisonExecution.width H=widthCoefficient*(H+1) := by
  dsimp [PlayerSpecificAlgebraicComparisonExecution.width,PlayerSpecificAlgebraicInitialPrimitiveCost.width,widthCoefficient]
  ring

theorem comparison (root : Candidate) (a b : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (ha : HasHeight a H) (hb : HasHeight b H)
    (hal : a.length≤3) (hbl : b.length≤3) (hH : 1≤H) :
    (PlayerSpecificAlgebraicComparisonExecution.run RationalCostModel.schoolbook root a b).2≤comparisonCoefficient*(H+1)^3 := by
  have hc:=PlayerSpecificAlgebraicComparisonExecution.cost RationalCostModel.schoolbook root a b H hm hm0 hml hmH he hv ha hb hal hbl hH
  rw [width_linear] at hc
  exact hc.trans (PlayerSpecificAlgebraicPairCost.cubic_profile _ _ _ (by omega))

theorem active (root : Candidate) (length resource : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hl : HasHeight length H) (hr : HasHeight resource H)
    (hll : length.length≤3) (hrl : resource.length≤3) (hH : 1≤H) :
    (PlayerSpecificAlgebraicComparisonExecution.active RationalCostModel.schoolbook root length resource).2≤activeCoefficient*(H+1)^3 := by
  have hc:=PlayerSpecificAlgebraicActiveCost.cost RationalCostModel.schoolbook root length resource H hm hm0 hml hmH he hv hl hr hll hrl hH
  rw [width_linear] at hc
  exact hc.trans (PlayerSpecificAlgebraicPairCost.cubic_profile _ _ _ (by omega))

end Blotto.PlayerSpecificAlgebraicComparisonCost
