import Blotto.PlayerSpecificInterpolationCoordinateExecution

/-! One actual affine-coordinate interpolation has a complete cubic
source price in the cached scalar/endpoint input height. -/
namespace Blotto.PlayerSpecificInterpolationCoordinateSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 13*PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 2+2
theorem profile (C X : ℕ) (h : 1≤X) : C*X+2≤(C+2)*X := by nlinarith only [h]

theorem cost (root : Candidate) (left right first second : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi)
    (hl : Reduced root.polynomial left ∧ HasHeight left H) (hr : Reduced root.polynomial right ∧ HasHeight right H)
    (hp : Reduced root.polynomial first ∧ HasHeight first H) (hq : Reduced root.polynomial second ∧ HasHeight second H) :
    (PlayerSpecificInterpolationCoordinateExecution.run RationalCostModel.schoolbook root left right first second).2≤coefficient*(H+16)^3 := by
  have hEnv : ∀ j,Reduced root.polynomial ((PlayerSpecificInterpolationCoordinateExecution.environment left right first second).read j) ∧
      HasHeight ((PlayerSpecificInterpolationCoordinateExecution.environment left right first second).read j) H := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificInterpolationCoordinateExecution.environment,FixedArrayTable.read_ofFn] using hl
    · simpa [PlayerSpecificInterpolationCoordinateExecution.environment,FixedArrayTable.read_ofFn] using hr
    · simpa [PlayerSpecificInterpolationCoordinateExecution.environment,FixedArrayTable.read_ofFn] using hp
    · simpa [PlayerSpecificInterpolationCoordinateExecution.environment,FixedArrayTable.read_ofFn] using hq
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root
    (PlayerSpecificInterpolationCoordinateExecution.environment left right first second) PlayerSpecificInterpolationCoordinateExecution.programs H 2
    hm hm0 hml hmH he hv hEnv PlayerSpecificInterpolationCoordinateExecution.depth
    (fun j => PlayerSpecificInterpolationCoordinateExecution.literals j H)
  rw [PlayerSpecificInterpolationCoordinateExecution.operations,show H+1+4+11=H+16 by omega] at hc
  change _≤(13*PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 2)*(H+16)^3 at hc
  change _+PlayerSpecificRationalTrace.price RationalCostModel.schoolbook [.control 0]≤_
  rw [PlayerSpecificInterpolationCoordinateExecution.packing]
  exact (Nat.add_le_add_right hc 2).trans (profile _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+16) 3)))

end Blotto.PlayerSpecificInterpolationCoordinateSourceCost
