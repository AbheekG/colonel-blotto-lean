import Blotto.PlayerSpecificNestedSecondInputExecution

/-! Complete second uniform input construction has a cubic price
from original raw rows and its retained mirror parameter. -/
namespace Blotto.PlayerSpecificNestedSecondInputSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := (PlayerSpecificExpressionVectorExecution.operations PlayerSpecificNestedSecondInputExecution.programs+5+5+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 1+10
theorem profile (C X : ℕ) (hX : 1≤X) : C*X+10≤(C+10)*X := by nlinarith only [hX]

theorem cost (root : Candidate) (a : Input) (p : Prepared) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H) (ha : Fits root a H)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p H) :
    (PlayerSpecificNestedSecondInputExecution.run RationalCostModel.schoolbook root a p).2≤coefficient*(H+21)^3 := by
  have henv : ∀ j,Reduced root.polynomial ((PlayerSpecificNestedSecondInputExecution.environment a p).read j) ∧
      HasHeight ((PlayerSpecificNestedSecondInputExecution.environment a p).read j) H := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificNestedSecondInputExecution.environment,FixedArrayTable.read_ofFn] using ha.budget
    · simpa [PlayerSpecificNestedSecondInputExecution.environment,FixedArrayTable.read_ofFn] using ha.first
    · simpa [PlayerSpecificNestedSecondInputExecution.environment,FixedArrayTable.read_ofFn] using ha.second
    · simpa [PlayerSpecificNestedSecondInputExecution.environment,FixedArrayTable.read_ofFn] using ha.short
    · simpa [PlayerSpecificNestedSecondInputExecution.environment,FixedArrayTable.read_ofFn] using hp.mirror
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (PlayerSpecificNestedSecondInputExecution.environment a p)
    PlayerSpecificNestedSecondInputExecution.programs H 1 hm hm0 hml hmH he hv henv PlayerSpecificNestedSecondInputExecution.depth
    (fun j => PlayerSpecificNestedSecondInputExecution.literals j H hH)
  rw [show H+5+5+11=H+21 by omega] at hc
  change _+price RationalCostModel.schoolbook (List.replicate 5 (.control 0))≤_
  rw [PlayerSpecificNestedSecondInputExecution.packing]
  exact (Nat.add_le_add_right hc 10).trans (profile _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+21) 3)))

end Blotto.PlayerSpecificNestedSecondInputSourceCost
