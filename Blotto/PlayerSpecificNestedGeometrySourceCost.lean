import Blotto.PlayerSpecificNestedGeometryExecution

/-! Complete conditional geometry source prices compose the actual
cached calls. All geometry and shift heights derive from raw inputs. -/
namespace Blotto.PlayerSpecificNestedGeometrySourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificNestedParameterSourceCost.firstCoefficient*(H+22)^3+
  PlayerSpecificThreeGeometrySourceCost.coefficient*(iterate 4 H+27)^3+
  PlayerSpecificDescriptorShiftSourceCost.work (iterate 21 H) 9+2

theorem geometry_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 2≤H) (ha : Fits root a H)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra H) :
    Bounds root (PlayerSpecificThreeGeometryExecution.run model root (firstEnvironment model root a extra)).1 (iterate 21 H) := by
  rw [PlayerSpecificThreeGeometryExecution.value]
  have henv:=first_environment_bounds model root a extra H ha hExtra hm hm0 hml hmH hH
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 4 H
  have hr:=PlayerSpecificAlgebraicThreeGeometry.reduced model root (firstEnvironment model root a extra) hm hm0 (fun j => (henv j).1)
  have hh:=PlayerSpecificAlgebraicThreeGeometry.heights model root (firstEnvironment model root a extra) hm hm0 hml
    (iterate 4 H) (mono hmH hbase) (hH.trans hbase) henv
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hh
  exact ⟨fun slot => ⟨hr.1 slot,hh.1 slot⟩,fun slot j => ⟨hr.2.1 slot j,hh.2.1 slot j⟩,
    fun slot j => ⟨hr.2.2 slot j,hh.2.2 slot j⟩⟩

theorem cost (root : Candidate) (a : Input) (extra : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra H) :
    (PlayerSpecificNestedGeometryExecution.run RationalCostModel.schoolbook root a extra).2≤work H := by
  let model:=RationalCostModel.schoolbook
  have hbase4:=PlayerSpecificAlgebraicExpressionBudget.initial_le 4 H
  have hbase21:=PlayerSpecificAlgebraicExpressionBudget.initial_le 21 H
  have henv:=first_environment_bounds model root a extra H ha hExtra hm hm0 hml hmH hH
  have hec:=PlayerSpecificNestedParameterSourceCost.first_cost root a extra H hm hm0 hml hmH he hv hH ha hExtra
  have hgc:=PlayerSpecificThreeGeometrySourceCost.cost root (firstEnvironment model root a extra) (iterate 4 H)
    hm hm0 hml (mono hmH hbase4) (mono he hbase4) hv (hH.trans hbase4) henv
  have hsc:=PlayerSpecificDescriptorShiftSourceCost.cost root extra
    (PlayerSpecificThreeGeometryExecution.run model root (firstEnvironment model root a extra)).1 (iterate 21 H)
    hm hm0 hml (mono hmH hbase21) (mono he hbase21) hv ⟨hExtra.1,mono hExtra.2 hbase21⟩
    (geometry_bounds model root a extra H hm hm0 hml hmH hH ha hExtra)
  rw [PlayerSpecificNestedGeometryExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hec hgc) hsc) 2

end Blotto.PlayerSpecificNestedGeometrySourceCost
