import Blotto.PlayerSpecificThreeGeometryExecution

/-! Complete original-row-height source work for the actual retained
nine-segment geometry table, including every executed expression and
all cached weight/endpoint arrays. -/
namespace Blotto.PlayerSpecificThreeGeometrySourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates RationalThreeGeometryCode
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := (PlayerSpecificThreeGeometryExecution.operationCount+4+9*(2*3+1)+1)*
  PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient 16

theorem cost (root : Candidate) (env : FixedArrayTable 4 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    (PlayerSpecificThreeGeometryExecution.run RationalCostModel.schoolbook root env).2≤coefficient*(H+27)^3 := by
  have hw : ∀ slot,((PlayerSpecificThreeGeometryExecution.weights.read slot).depth≤16 ∧
      (PlayerSpecificThreeGeometryExecution.weights.read slot).LiteralHeights H) := by
    intro slot
    rw [PlayerSpecificThreeGeometryExecution.weights,FixedArrayTable.read_ofFn]
    exact ⟨chosen_depth slot,(chosen slot).LiteralHeights_mono hH (chosen_literals slot)⟩
  have hp : ∀ slot j,(((PlayerSpecificThreeGeometryExecution.first.read slot).read j).depth≤16 ∧
      ((PlayerSpecificThreeGeometryExecution.first.read slot).read j).LiteralHeights H) := by
    intro slot j
    rw [PlayerSpecificThreeGeometryExecution.first,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact ⟨(vertex_depth _ j).trans (by decide : 2≤16),(vertex _ j).LiteralHeights_mono hH (vertex_literals _ j)⟩
  have hq : ∀ slot j,(((PlayerSpecificThreeGeometryExecution.second.read slot).read j).depth≤16 ∧
      ((PlayerSpecificThreeGeometryExecution.second.read slot).read j).LiteralHeights H) := by
    intro slot j
    rw [PlayerSpecificThreeGeometryExecution.second,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact ⟨(vertex_depth _ j).trans (by decide : 2≤16),(vertex _ j).LiteralHeights_mono hH (vertex_literals _ j)⟩
  have hc:=PlayerSpecificDescriptorProgramSourceCost.polynomial_cost root env
    PlayerSpecificThreeGeometryExecution.weights PlayerSpecificThreeGeometryExecution.first PlayerSpecificThreeGeometryExecution.second
    H 16 hm hm0 hml hmH he hv hEnv hw hp hq
  change _≤coefficient*(H+9+3+4+11)^3 at hc
  rw [show H+9+3+4+11=H+27 by omega] at hc
  exact hc

theorem same_return_and_cost (root : Candidate) (env : FixedArrayTable 4 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    (PlayerSpecificThreeGeometryExecution.run RationalCostModel.schoolbook root env).1=
      PlayerSpecificAlgebraicThreeGeometry.prepare RationalCostModel.schoolbook root env ∧
    (PlayerSpecificThreeGeometryExecution.run RationalCostModel.schoolbook root env).2≤coefficient*(H+27)^3 :=
  ⟨PlayerSpecificThreeGeometryExecution.value _ root env,cost root env H hm hm0 hml hmH he hv hH hEnv⟩

end Blotto.PlayerSpecificThreeGeometrySourceCost
