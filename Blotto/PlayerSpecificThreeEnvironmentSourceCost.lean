import Blotto.PlayerSpecificThreeEnvironmentExecution

/-! The measured geometry environment is polynomial in its actual raw
input height, including input/result arrays and all four local programs. -/
namespace Blotto.PlayerSpecificThreeEnvironmentSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := (PlayerSpecificExpressionVectorExecution.operations PlayerSpecificThreeEnvironmentExecution.programs+5+4+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 3

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H) (ha : PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root a H) :
    (PlayerSpecificThreeEnvironmentExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+20)^3 := by
  have hEnv : ∀ j,Reduced root.polynomial ((PlayerSpecificThreeEnvironmentExecution.input a).read j) ∧
      HasHeight ((PlayerSpecificThreeEnvironmentExecution.input a).read j) H := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.budget
    · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.first
    · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.second
    · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.third
    · simpa [PlayerSpecificThreeEnvironmentExecution.input,FixedArrayTable.read_ofFn] using ha.probability
  have hc:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (PlayerSpecificThreeEnvironmentExecution.input a)
    PlayerSpecificThreeEnvironmentExecution.programs H 3 hm hm0 hml hmH he hv hEnv PlayerSpecificThreeEnvironmentExecution.depth
      (fun j => (PlayerSpecificThreeEnvironmentExecution.programs.read j).LiteralHeights_mono hH (PlayerSpecificThreeEnvironmentExecution.literals j))
  change _≤coefficient*(H+4+5+11)^3 at hc
  rw [show H+4+5+11=H+20 by omega] at hc
  exact hc

end Blotto.PlayerSpecificThreeEnvironmentSourceCost
