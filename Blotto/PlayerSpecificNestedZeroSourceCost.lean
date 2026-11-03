import Blotto.PlayerSpecificNestedZeroExecution

/-! The complete zero-corner price uses original raw height only;
literal weights and every copied endpoint/result row are included. -/
namespace Blotto.PlayerSpecificNestedZeroSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def weightsCoefficient : ℕ := (PlayerSpecificExpressionVectorExecution.operations PlayerSpecificNestedZeroExecution.programs+7+9+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 0
def work (H : ℕ) : ℕ := weightsCoefficient*(H+27)^3+
  PlayerSpecificDescriptorCopySourceCost.coefficient*(iterate 22 H+20)^5

theorem cost (root : Candidate) (a : Input) (extra : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra H) :
    (PlayerSpecificNestedZeroExecution.run RationalCostModel.schoolbook root a extra).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificNestedZeroExecution.run model root a extra).1
  have henv:=environment_bounds root a extra H ha hExtra
  have hw:=PlayerSpecificExpressionVectorSourceCost.polynomial_cost root (environment a extra) PlayerSpecificNestedZeroExecution.programs H 0
    hm hm0 hml hmH he hv henv PlayerSpecificNestedZeroExecution.depth
    (fun j => (PlayerSpecificNestedZeroExecution.programs.read j).LiteralHeights_mono (show 1≤H by omega) (PlayerSpecificNestedZeroExecution.literals j))
  change _≤weightsCoefficient*(H+9+7+11)^3 at hw
  rw [show H+9+7+11=H+27 by omega] at hw
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 22 H
  have hd : PlayerSpecificAlgebraicDescriptorBounds.Bounds root result (iterate 22 H) := by
    change PlayerSpecificAlgebraicDescriptorBounds.Bounds root (PlayerSpecificNestedZeroExecution.run model root a extra).1 (iterate 22 H)
    rw [PlayerSpecificNestedZeroExecution.value]
    exact PlayerSpecificAlgebraicNestedFirstSizes.zero root a extra H ha hExtra hm hm0 hml hmH hH
  have hf:=PlayerSpecificDescriptorCopySourceCost.cost root (environment a extra) result (iterate 22 H)
    (mono hmH hbase) hml (mono he hbase) (fun j => ⟨(henv j).1,mono (henv j).2 hbase⟩) hd
  rw [show iterate 22 H+3+9+7+1=iterate 22 H+20 by omega] at hf
  exact Nat.add_le_add hw hf

end Blotto.PlayerSpecificNestedZeroSourceCost
