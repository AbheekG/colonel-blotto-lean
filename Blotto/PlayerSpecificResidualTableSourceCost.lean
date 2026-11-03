import Blotto.PlayerSpecificResidualTableExecution

/-! Complete residual-table work from original raw nested rows. The
environment height is derived internally from its actual computation. -/
namespace Blotto.PlayerSpecificResidualTableSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def tableCoefficient : ℕ := (PlayerSpecificDescriptorProgramExecution.operations PlayerSpecificResidualTableExecution.weights
  PlayerSpecificResidualTableExecution.first PlayerSpecificResidualTableExecution.second+5+3*(2*3+1)+1)*
    PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 8
def coefficient : ℕ := PlayerSpecificResidualEnvironmentSourceCost.coefficient*23^3+
  tableCoefficient*((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^2+22)^3+6

theorem profile (G T X : ℕ) (hX : 1≤X) : G*X+T*X+6≤(G+T+6)*X := by
  nlinarith only [hX]

theorem table_cost (root : Candidate) (env : FixedArrayTable 5 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    (PlayerSpecificDescriptorProgramExecution.run RationalCostModel.schoolbook root env
      PlayerSpecificResidualTableExecution.weights PlayerSpecificResidualTableExecution.first PlayerSpecificResidualTableExecution.second).2≤
        tableCoefficient*(H+22)^3 := by
  have hw : ∀ slot,(PlayerSpecificResidualTableExecution.weights.read slot).depth≤8 ∧
      (PlayerSpecificResidualTableExecution.weights.read slot).LiteralHeights H := by
    intro slot
    rw [PlayerSpecificResidualTableExecution.weights,FixedArrayTable.read_ofFn]
    exact ⟨RationalNestedResidualCode.weight_depth slot,
      (RationalNestedResidualCode.weights slot).LiteralHeights_mono hH (RationalNestedResidualCode.weight_literals slot)⟩
  have hp : ∀ slot j,((PlayerSpecificResidualTableExecution.first.read slot).read j).depth≤8 ∧
      ((PlayerSpecificResidualTableExecution.first.read slot).read j).LiteralHeights H := by
    intro slot j
    rw [PlayerSpecificResidualTableExecution.first,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact ⟨(RationalNestedResidualCode.vertex_depth _ j).trans (by decide : 3≤8),
      (RationalNestedResidualCode.vertices _ j).LiteralHeights_mono hH (RationalNestedResidualCode.vertex_literals _ j)⟩
  have hq : ∀ slot j,((PlayerSpecificResidualTableExecution.second.read slot).read j).depth≤8 ∧
      ((PlayerSpecificResidualTableExecution.second.read slot).read j).LiteralHeights H := by
    intro slot j
    rw [PlayerSpecificResidualTableExecution.second,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact ⟨(RationalNestedResidualCode.vertex_depth _ j).trans (by decide : 3≤8),
      (RationalNestedResidualCode.vertices _ j).LiteralHeights_mono hH (RationalNestedResidualCode.vertex_literals _ j)⟩
  have hc:=PlayerSpecificDescriptorProgramSourceCost.polynomial_cost root env PlayerSpecificResidualTableExecution.weights
    PlayerSpecificResidualTableExecution.first PlayerSpecificResidualTableExecution.second H 8 hm hm0 hml hmH he hv hEnv hw hp hq
  change _≤tableCoefficient*(H+3+3+5+11)^3 at hc
  rw [show H+3+3+5+11=H+22 by omega] at hc
  exact hc

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificResidualTableExecution.run RationalCostModel.schoolbook root a).2≤coefficient*(H+1)^3 := by
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 2 H
  have henv:=PlayerSpecificAlgebraicResidualEnvironment.bounds root a H ha hm hm0 hml hmH
  have hec:=PlayerSpecificResidualEnvironmentSourceCost.cost root a H hm hm0 hml hmH he hv ha
  have htc:=table_cost root (PlayerSpecificAlgebraicResidualEnvironment.environment root a) (iterate 2 H)
    hm hm0 hml (mono hmH hbase) (mono he hbase) hv (hH.trans hbase) henv
  have hec':=hec.trans (PlayerSpecificThreePreparationInputs.transfer _ 23 H (H+23) (by omega))
  have htc':=htc.trans (PlayerSpecificThreePreparationInputs.transfer _ _ H (iterate 2 H+22)
    (PlayerSpecificThreePreparationInputs.shift 2 H 22))
  have hc:=Nat.add_le_add_right (Nat.add_le_add hec' htc') 6
  change (PlayerSpecificResidualEnvironmentExecution.run RationalCostModel.schoolbook root a).2+
    (PlayerSpecificDescriptorProgramExecution.run RationalCostModel.schoolbook root
      (PlayerSpecificResidualEnvironmentExecution.run RationalCostModel.schoolbook root a).1
      PlayerSpecificResidualTableExecution.weights PlayerSpecificResidualTableExecution.first PlayerSpecificResidualTableExecution.second).2+
      price RationalCostModel.schoolbook (List.replicate 3 (.control 0))≤_
  rw [PlayerSpecificResidualEnvironmentExecution.value,PlayerSpecificResidualTableExecution.packing]
  exact hc.trans (profile _ _ _ (Nat.succ_le_of_lt (pow_pos (by omega : 0<H+1) 3)))

end Blotto.PlayerSpecificResidualTableSourceCost
