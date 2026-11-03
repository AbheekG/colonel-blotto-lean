import Blotto.PlayerSpecificNestedSecondUniformExecution

/-! Complete uniform-component source work derives the reached input
and descriptor heights from the original raw rows and case record. -/
namespace Blotto.PlayerSpecificNestedSecondUniformSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificNestedSecondInputSourceCost.coefficient*(H+21)^3+
  PlayerSpecificOrderedThreeSourceCost.coefficient*(step H+1)^3+PlayerSpecificDescriptorShiftSourceCost.work (iterate 21 H) 9+2

theorem ordered_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 2≤H) (ha : Fits root a H)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p H) :
    Bounds root (PlayerSpecificOrderedThreeExecution.run model root (PlayerSpecificAlgebraicNestedSecondUniform.input root a p)).1 (iterate 21 H) := by
  rw [PlayerSpecificOrderedThreeExecution.value]
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 1 H
  have hi:=PlayerSpecificAlgebraicNestedSecondSizes.input_bounds root a p H ha hp hm hm0 hml hmH (by omega)
  have hd:=PlayerSpecificAlgebraicThreeDescriptorSizes.ordered model root (PlayerSpecificAlgebraicNestedSecondUniform.input root a p)
    (step H) hi hm hm0 hml (mono hmH hbase) (hH.trans hbase)
  change Bounds root _ (iterate 20 (iterate 1 H)) at hd
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hd
  exact hd

theorem cost (root : Candidate) (a : Input) (p : Prepared) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p H) :
    (PlayerSpecificNestedSecondUniformExecution.run RationalCostModel.schoolbook root a p).2≤work H := by
  let model:=RationalCostModel.schoolbook
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 1 H
  have h21:=PlayerSpecificAlgebraicExpressionBudget.initial_le 21 H
  have hi:=PlayerSpecificAlgebraicNestedSecondSizes.input_bounds root a p H ha hp hm hm0 hml hmH (by omega)
  have hic:=PlayerSpecificNestedSecondInputSourceCost.cost root a p H hm hm0 hml hmH he hv (by omega) ha hp
  have hoc:=PlayerSpecificOrderedThreeSourceCost.cost root (PlayerSpecificAlgebraicNestedSecondUniform.input root a p) (step H)
    hm hm0 hml (mono hmH hbase) (mono he hbase) hv (hH.trans hbase) hi
  have hsc:=PlayerSpecificDescriptorShiftSourceCost.cost root p.mirror
    (PlayerSpecificOrderedThreeExecution.run model root (PlayerSpecificAlgebraicNestedSecondUniform.input root a p)).1 (iterate 21 H)
    hm hm0 hml (mono hmH h21) (mono he h21) hv ⟨hp.mirror.1,mono hp.mirror.2 h21⟩
    (ordered_bounds model root a p H hm hm0 hml hmH hH ha hp)
  rw [PlayerSpecificNestedSecondUniformExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hic hoc) hsc) 2

end Blotto.PlayerSpecificNestedSecondUniformSourceCost
