import Blotto.PlayerSpecificDescriptorShiftRowExecution

/-! Original-row-height source price for the actual shifted endpoint. -/
namespace Blotto.PlayerSpecificDescriptorShiftRowSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 13*PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 1

theorem cost (root : Candidate) (s : Data) (a : FixedArrayTable 3 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi)
    (hs : Reduced root.polynomial s ∧ HasHeight s H)
    (ha : ∀ j,Reduced root.polynomial (a.read j) ∧ HasHeight (a.read j) H) :
    (PlayerSpecificDescriptorShiftRowExecution.run RationalCostModel.schoolbook root s a).2≤coefficient*(H+18)^3 := by
  have hEnv : ∀ j,Reduced root.polynomial ((PlayerSpecificDescriptorShiftRowExecution.environment s a).read j) ∧
      HasHeight ((PlayerSpecificDescriptorShiftRowExecution.environment s a).read j) H := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificDescriptorShiftRowExecution.environment,FixedArrayTable.read_ofFn] using ha 0
    · simpa [PlayerSpecificDescriptorShiftRowExecution.environment,FixedArrayTable.read_ofFn] using ha 1
    · simpa [PlayerSpecificDescriptorShiftRowExecution.environment,FixedArrayTable.read_ofFn] using ha 2
    · simpa [PlayerSpecificDescriptorShiftRowExecution.environment,FixedArrayTable.read_ofFn] using hs
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root
    (PlayerSpecificDescriptorShiftRowExecution.environment s a) PlayerSpecificDescriptorShiftRowExecution.programs H 1
    hm hm0 hml hmH he hv hEnv PlayerSpecificDescriptorShiftRowExecution.depth
    (fun j => PlayerSpecificDescriptorShiftRowExecution.literals j H)
  rw [PlayerSpecificDescriptorShiftRowExecution.operations,show H+3+4+11=H+18 by omega] at hc
  exact hc

end Blotto.PlayerSpecificDescriptorShiftRowSourceCost
