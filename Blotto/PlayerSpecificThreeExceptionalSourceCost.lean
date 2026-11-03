import Blotto.PlayerSpecificThreeExceptionalExecution

/-! Complete exceptional preparation work, including literal weights,
literal-zero endpoint arrays and the full retained return frame. -/
namespace Blotto.PlayerSpecificThreeExceptionalSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def weightsCoefficient : ℕ := ((PlayerSpecificExpressionVectorExecution.operations PlayerSpecificThreeExceptionalExecution.programs+5+9+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 0)*25^3
def coefficient : ℕ := weightsCoefficient+PlayerSpecificThreePreparationInputs.frameCoefficient

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root a H) :
    (PlayerSpecificThreeExceptionalExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+1)^3 := by
  have hw:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (PlayerSpecificThreeEnvironmentExecution.input a)
    PlayerSpecificThreeExceptionalExecution.programs H 0 hm hm0 hml hmH he hv (PlayerSpecificThreePreparationInputs.raw ha)
    PlayerSpecificThreeExceptionalExecution.depth
    (fun j => (PlayerSpecificThreeExceptionalExecution.programs.read j).LiteralHeights_mono (show 1≤H by omega) (PlayerSpecificThreeExceptionalExecution.literals j))
  rw [show H+9+5+11=H+25 by omega] at hw
  have hwQ : (PlayerSpecificExpressionVectorExecution.run RationalCostModel.schoolbook root (PlayerSpecificThreeEnvironmentExecution.input a)
      PlayerSpecificThreeExceptionalExecution.programs).2≤weightsCoefficient*(H+1)^3 :=
    hw.trans (PlayerSpecificThreePreparationInputs.transfer _ 25 H (H+25) (by omega))
  have hd : PlayerSpecificAlgebraicDescriptorBounds.Bounds root (PlayerSpecificThreeExceptionalExecution.run RationalCostModel.schoolbook root a).1
      (PlayerSpecificAlgebraicHeightEnvelope.iterate 20 H) := by
    rw [PlayerSpecificThreeExceptionalExecution.value]
    exact PlayerSpecificAlgebraicThreeDescriptorSizes.exceptional root a H ha hm hm0 hml hmH hH
  have hf:=PlayerSpecificThreePreparationInputs.frame_polynomial root a
    (PlayerSpecificThreeExceptionalExecution.run RationalCostModel.schoolbook root a).1 H hmH hml he ha hd
  exact (Nat.add_le_add hwQ hf).trans_eq (Nat.add_mul _ _ _).symm

end Blotto.PlayerSpecificThreeExceptionalSourceCost
