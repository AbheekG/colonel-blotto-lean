import Blotto.PlayerSpecificOverlapRowExecution

/-! Complete overlap-row source work includes all selected conditional
continuations, total divisions, zero corners and safe endpoint returns. -/
namespace Blotto.PlayerSpecificOverlapRowSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def tableCoefficient : ℕ := (PlayerSpecificOverlapRowExecution.operationCount+16+1*(2*4+1)+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 9
def coefficient : ℕ := tableCoefficient+6

theorem cost (root : Candidate) (env : FixedArrayTable 16 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    (PlayerSpecificOverlapRowExecution.run RationalCostModel.schoolbook root env).2≤coefficient*(H+32)^3 := by
  have hw : ∀ slot,(PlayerSpecificOverlapRowExecution.weights.read slot).depth≤9 ∧
      (PlayerSpecificOverlapRowExecution.weights.read slot).LiteralHeights H := by
    intro slot
    rw [PlayerSpecificOverlapRowExecution.weights,FixedArrayTable.read_ofFn]
    exact ⟨OverlapFormulaCode.weight_depth.trans (by decide : 7≤9),
      OverlapFormulaCode.weight.LiteralHeights_mono hH OverlapFormulaCode.weight_literals⟩
  have hp : ∀ slot j,((PlayerSpecificOverlapRowExecution.first.read slot).read j).depth≤9 ∧
      ((PlayerSpecificOverlapRowExecution.first.read slot).read j).LiteralHeights H := by
    intro slot j
    rw [PlayerSpecificOverlapRowExecution.first,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact ⟨OverlapFormulaCode.safeP_depth j,(OverlapFormulaCode.safeP j).LiteralHeights_mono hH (OverlapFormulaCode.safeP_literals j)⟩
  have hq : ∀ slot j,((PlayerSpecificOverlapRowExecution.second.read slot).read j).depth≤9 ∧
      ((PlayerSpecificOverlapRowExecution.second.read slot).read j).LiteralHeights H := by
    intro slot j
    rw [PlayerSpecificOverlapRowExecution.second,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact ⟨OverlapFormulaCode.safeQ_depth j,(OverlapFormulaCode.safeQ j).LiteralHeights_mono hH (OverlapFormulaCode.safeQ_literals j)⟩
  have hc:=PlayerSpecificDescriptorProgramSourceCost.polynomial_cost root env PlayerSpecificOverlapRowExecution.weights
    PlayerSpecificOverlapRowExecution.first PlayerSpecificOverlapRowExecution.second H 9 hm hm0 hml hmH he hv hEnv hw hp hq
  change _≤tableCoefficient*(H+1+4+16+11)^3 at hc
  rw [show H+1+4+16+11=H+32 by omega] at hc
  have hpos : 1≤(H+32)^3 := Nat.succ_le_of_lt (pow_pos (by omega : 0<H+32) 3)
  change (PlayerSpecificDescriptorProgramExecution.run RationalCostModel.schoolbook root env PlayerSpecificOverlapRowExecution.weights
    PlayerSpecificOverlapRowExecution.first PlayerSpecificOverlapRowExecution.second).2+
      PlayerSpecificRationalTrace.price RationalCostModel.schoolbook [.control 0,.control 0,.control 0]≤_
  rw [PlayerSpecificOverlapRowExecution.packing]
  change _≤(tableCoefficient+6)*(H+32)^3
  nlinarith only [hc,hpos]

end Blotto.PlayerSpecificOverlapRowSourceCost
