import Blotto.PlayerSpecificNestedEndpointProfileExecution

/-! Complete endpoint profile work derives its input and table sizes
from the original raw rows, for both closed-probability endpoints. -/
namespace Blotto.PlayerSpecificNestedEndpointProfileSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificNestedEndpointInputSourceCost.coefficient*(H+23)^3+
  PlayerSpecificUnorderedThreeSourceCost.coefficient*(step H+1)^3+PlayerSpecificDescriptorPadSourceCost.work (iterate 21 H) 3 9 9+2

theorem table_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (useShort : Bool) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 2≤H) (ha : Fits root a H) :
    Bounds root (PlayerSpecificUnorderedThreeExecution.run model root (PlayerSpecificAlgebraicNestedSpecInput.endpoint root a useShort)).1 (iterate 21 H) := by
  rw [PlayerSpecificUnorderedThreeExecution.value]
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 1 H
  have hi:=PlayerSpecificAlgebraicNestedSpecInputSizes.endpoint_fits root a useShort H ha hm hm0 hml hmH (by omega)
  have hd:=PlayerSpecificAlgebraicThreeDescriptorSizes.unordered model root (PlayerSpecificAlgebraicNestedSpecInput.endpoint root a useShort)
    (step H) hi hm hm0 hml (mono hmH hbase) (hH.trans hbase)
  change Bounds root _ (iterate 20 (iterate 1 H)) at hd
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hd
  exact hd

theorem cost (root : Candidate) (a : Input) (useShort : Bool) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedEndpointProfileExecution.run RationalCostModel.schoolbook root a useShort).2≤work H := by
  let model:=RationalCostModel.schoolbook
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 1 H
  have h21:=PlayerSpecificAlgebraicExpressionBudget.initial_le 21 H
  have hi:=PlayerSpecificAlgebraicNestedSpecInputSizes.endpoint_fits root a useShort H ha hm hm0 hml hmH (by omega)
  have hic:=PlayerSpecificNestedEndpointInputSourceCost.cost root a useShort H hm hm0 hml hmH he hv (by omega) ha
  have htc:=PlayerSpecificUnorderedThreeSourceCost.cost root (PlayerSpecificAlgebraicNestedSpecInput.endpoint root a useShort) (step H)
    hm hm0 hml (mono hmH hbase) (mono he hbase) hv (hH.trans hbase) hi
  have hpc:=PlayerSpecificDescriptorPadSourceCost.cost root
    (PlayerSpecificUnorderedThreeExecution.run model root (PlayerSpecificAlgebraicNestedSpecInput.endpoint root a useShort)).1 9 0 (iterate 21 H)
    hm0 hml (mono hmH h21) (mono he h21) (table_bounds model root a useShort H hm hm0 hml hmH hH ha)
  rw [PlayerSpecificNestedEndpointProfileExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hic htc) hpc) 2

end Blotto.PlayerSpecificNestedEndpointProfileSourceCost
