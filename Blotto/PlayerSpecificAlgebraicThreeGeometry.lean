import Blotto.PlayerSpecificAlgebraicSegment
import Blotto.RealThreeGeometryCompiler

/-! The retained nine-segment three-variable formula table now executes
in the actual algebraic field. The four-entry environment is cached and
the same fixed local programs produce every weight and endpoint. -/
namespace Blotto.PlayerSpecificAlgebraicThreeGeometry
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicCandidates (Candidate)
open RationalThreeGeometryCode
set_option autoImplicit false
set_option maxHeartbeats 2500000

abbrev Descriptor := PlayerSpecificAlgebraicSegment.Descriptor 3 9

def prepare (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data) : Descriptor :=
  ⟨FixedArrayTable.ofFn (fun slot => PlayerSpecificAlgebraicExpression.run model root env (chosen slot)),
    FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j =>
      PlayerSpecificAlgebraicExpression.run model root env (vertex (RationalThreeGeometry.edges slot).1 j))),
    FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j =>
      PlayerSpecificAlgebraicExpression.run model root env (vertex (RationalThreeGeometry.edges slot).2 j)))⟩

theorem fields (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j)) (g : ThreeGeometry)
    (he : PlayerSpecificAlgebraicExpression.realEnv env x=RealThreeGeometryCode.environment g) :
    (∀ slot,realEvaluate ((prepare model root env).weights.read slot) x=g.chosenWeights.vector slot) ∧
      (∀ slot j,realEvaluate (((prepare model root env).first.read slot).read j) x=g.vertex (RationalThreeGeometry.edges slot).1 j) ∧
      (∀ slot j,realEvaluate (((prepare model root env).second.read slot).read j) x=g.vertex (RationalThreeGeometry.edges slot).2 j) := by
  constructor
  · intro slot
    simp only [prepare,FixedArrayTable.read_ofFn]
    rw [PlayerSpecificAlgebraicExpressionValue.value model root env (chosen slot) hm hirr hv x hx hEnv,he]
    exact RealThreeGeometryCode.chosen_value g slot
  · constructor
    · intro slot j
      simp only [prepare,FixedArrayTable.read_ofFn]
      rw [PlayerSpecificAlgebraicExpressionValue.value model root env (vertex (RationalThreeGeometry.edges slot).1 j) hm hirr hv x hx hEnv,he]
      exact RealThreeGeometryCode.vertex_value g _ j
    · intro slot j
      simp only [prepare,FixedArrayTable.read_ofFn]
      rw [PlayerSpecificAlgebraicExpressionValue.value model root env (vertex (RationalThreeGeometry.edges slot).2 j) hm hirr hv x hx hEnv,he]
      exact RealThreeGeometryCode.vertex_value g _ j

theorem reduced (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hEnv : ∀ j,Reduced root.polynomial (env.read j)) :
    (∀ slot,Reduced root.polynomial ((prepare model root env).weights.read slot)) ∧
      (∀ slot j,Reduced root.polynomial (((prepare model root env).first.read slot).read j)) ∧
      (∀ slot j,Reduced root.polynomial (((prepare model root env).second.read slot).read j)) := by
  refine ⟨?_,?_,?_⟩
  · intro slot
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact PlayerSpecificAlgebraicExpression.reduced model root env (chosen slot) hm hm0 hEnv
  · intro slot j
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact PlayerSpecificAlgebraicExpression.reduced model root env (vertex (RationalThreeGeometry.edges slot).1 j) hm hm0 hEnv
  · intro slot j
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact PlayerSpecificAlgebraicExpression.reduced model root env (vertex (RationalThreeGeometry.edges slot).2 j) hm hm0 hEnv

theorem heights (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (T : ℕ) (hmT : HasHeight root.polynomial T) (hT : 2≤T)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) T) :
    (∀ slot,HasHeight ((prepare model root env).weights.read slot) (PlayerSpecificAlgebraicHeightEnvelope.iterate 17 T)) ∧
      (∀ slot j,HasHeight (((prepare model root env).first.read slot).read j) (PlayerSpecificAlgebraicHeightEnvelope.iterate 17 T)) ∧
      (∀ slot j,HasHeight (((prepare model root env).second.read slot).read j) (PlayerSpecificAlgebraicHeightEnvelope.iterate 17 T)) := by
  have hrun:=fun e hLit => PlayerSpecificAlgebraicExpressionHeights.run_height model root env e hm hm0 hml T hmT
    (show 1≤T by omega) hEnv hLit
  refine ⟨?_,?_,?_⟩
  · intro slot
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact mono (hrun (chosen slot) ((chosen slot).LiteralHeights_mono hT (chosen_literals slot)))
      (PlayerSpecificAlgebraicExpressionBudget.depth_mono T (chosen_depth slot))
  · intro slot j
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact mono (hrun (vertex (RationalThreeGeometry.edges slot).1 j) ((vertex (RationalThreeGeometry.edges slot).1 j).LiteralHeights_mono hT (vertex_literals _ j)))
      (PlayerSpecificAlgebraicExpressionBudget.depth_mono T ((vertex_depth (RationalThreeGeometry.edges slot).1 j).trans (by decide : 2≤16)))
  · intro slot j
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact mono (hrun (vertex (RationalThreeGeometry.edges slot).2 j) ((vertex (RationalThreeGeometry.edges slot).2 j).LiteralHeights_mono hT (vertex_literals _ j)))
      (PlayerSpecificAlgebraicExpressionBudget.depth_mono T ((vertex_depth (RationalThreeGeometry.edges slot).2 j).trans (by decide : 2≤16)))

end Blotto.PlayerSpecificAlgebraicThreeGeometry
