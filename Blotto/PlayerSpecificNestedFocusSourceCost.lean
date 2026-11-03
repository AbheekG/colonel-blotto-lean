import Blotto.PlayerSpecificNestedFocusExecution

/-! Complete terminal focus work has a cubic source bound in the
original resource row height, with no active-test or size oracle. -/
namespace Blotto.PlayerSpecificNestedFocusSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedTerminalInput PlayerSpecificAlgebraicNestedTerminalSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def activeCoefficient : ℕ := (2*PlayerSpecificAlgebraicComparisonExecution.coefficient+3)*PlayerSpecificResourceCostProfile.rationalCoefficient
def work (H : ℕ) : ℕ := 2*(activeCoefficient*(H+1)^3)+7
theorem first_profile (A : ℕ) : A+7≤2*A+7 := by omega
theorem second_profile (A : ℕ) : A+A+7=2*A+7 := by omega

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedFocusExecution.run RationalCostModel.schoolbook root a).2≤work H := by
  let model:=RationalCostModel.schoolbook
  have hactive : ∀ j : Fin 3,(PlayerSpecificAlgebraicComparisonExecution.active model root (a.capacity.read j) (a.resource.read j)).2≤
      activeCoefficient*(H+1)^3 := by
    intro j
    exact (PlayerSpecificAlgebraicActiveCost.cost model root (a.capacity.read j) (a.resource.read j) H hm hm0 hml hmH he hv
      (ha.capacity j).2 (ha.resource j).2 (by have h:=(ha.capacity j).1.2; omega) (by have h:=(ha.resource j).1.2; omega) hH).trans
        (PlayerSpecificResourceCostProfile.cubic (2*PlayerSpecificAlgebraicComparisonExecution.coefficient+3) H)
  simp only [PlayerSpecificNestedFocusExecution.run]
  split
  · exact (Nat.add_le_add (hactive 0) (PlayerSpecificNestedFocusExecution.packing_cost model 0)).trans (first_profile _)
  · exact (Nat.add_le_add (Nat.add_le_add (hactive 0) (hactive 1)) (PlayerSpecificNestedFocusExecution.packing_cost model _)).trans_eq
      (second_profile _)

end Blotto.PlayerSpecificNestedFocusSourceCost
