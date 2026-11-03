import Blotto.PlayerSpecificFourParentInputExecution

/-! Complete parent-input construction has a cubic source price in
the retained original rows and shared parameter-table height. -/
namespace Blotto.PlayerSpecificFourParentInputSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 25*PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 0+12
theorem profile (C X : ℕ) (hX : 1≤X) : C*X+12≤(C+12)*X := by nlinarith only [hX]

theorem cost (root : Candidate) (a : Input) (p : FixedArrayTable 8 Data) (useSecond : Bool) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H) (ha : Fits root a H)
    (hp : ∀ j,Reduced root.polynomial (p.read j) ∧ HasHeight (p.read j) H) :
    (PlayerSpecificFourParentInputExecution.run RationalCostModel.schoolbook root a p useSecond).2≤coefficient*(H+30)^3 := by
  have hraw:=environment_bounds root a H ha
  have henv : ∀ j,Reduced root.polynomial ((PlayerSpecificFourParentInputExecution.environment a p).read j) ∧
      HasHeight ((PlayerSpecificFourParentInputExecution.environment a p).read j) H := by
    intro j
    refine Fin.addCases (m:=6) (n:=8) ?_ ?_ j
    · intro j; simpa only [PlayerSpecificFourParentInputExecution.environment,FixedArrayTable.read_ofFn,Fin.addCases_left] using hraw j
    · intro j; simpa only [PlayerSpecificFourParentInputExecution.environment,FixedArrayTable.read_ofFn,Fin.addCases_right] using hp j
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (PlayerSpecificFourParentInputExecution.environment a p)
    (PlayerSpecificFourParentInputExecution.programs useSecond) H 0 hm hm0 hml hmH he hv henv
    (PlayerSpecificFourParentInputExecution.depth useSecond) (fun j => PlayerSpecificFourParentInputExecution.literals useSecond j H hH)
  rw [PlayerSpecificFourParentInputExecution.operations,show H+5+14+11=H+30 by omega] at hc
  change _+price RationalCostModel.schoolbook (List.replicate 6 (.control 1))≤_
  rw [PlayerSpecificFourParentInputExecution.packing]
  exact (Nat.add_le_add_right hc 12).trans (profile _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+30) 3)))

end Blotto.PlayerSpecificFourParentInputSourceCost
