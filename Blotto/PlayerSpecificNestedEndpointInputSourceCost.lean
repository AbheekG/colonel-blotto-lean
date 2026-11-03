import Blotto.PlayerSpecificNestedEndpointInputExecution

/-! Complete source price of both actual endpoint input constructors,
with selected-length reads and all original/returned raw rows included. -/
namespace Blotto.PlayerSpecificNestedEndpointInputSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 18*PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 0+12
theorem profile (C X : ℕ) (hX : 1≤X) : C*X+12≤(C+12)*X := by nlinarith only [hX]

theorem cost (root : Candidate) (a : Input) (useShort : Bool) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedEndpointInputExecution.run RationalCostModel.schoolbook root a useShort).2≤coefficient*(H+23)^3 := by
  have henv:=environment_bounds root a [] H ha ⟨nil_reduced _ hm0,nil_height _⟩
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (environment a [])
    (PlayerSpecificNestedEndpointInputExecution.programs useShort) H 0 hm hm0 hml hmH he hv henv
    (PlayerSpecificNestedEndpointInputExecution.depth useShort) (fun j => PlayerSpecificNestedEndpointInputExecution.literals useShort j H hH)
  rw [PlayerSpecificNestedEndpointInputExecution.operations,show H+5+7+11=H+23 by omega] at hc
  change _+price RationalCostModel.schoolbook (List.replicate 6 (.control 1))≤_
  rw [PlayerSpecificNestedEndpointInputExecution.packing]
  exact (Nat.add_le_add_right hc 12).trans (profile _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+23) 3)))

end Blotto.PlayerSpecificNestedEndpointInputSourceCost
