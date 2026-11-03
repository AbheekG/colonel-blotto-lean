import Blotto.PlayerSpecificAlgebraicThreeGeometry
import Blotto.PlayerSpecificAlgebraicSegmentSample

/-! Actual bounded-bit sampling from the algebraic nine-segment table.
Every bit string gives a nonnegative full-budget point in the core box;
categorical/whole-law approximation and full source prices remain joins. -/
namespace Blotto.PlayerSpecificAlgebraicThreeGeometrySample
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicThreeGeometry
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data) (H K : ℕ)
    (bits : Fin (8*H+K) → Bool) : FixedArrayTable 3 Data :=
  PlayerSpecificAlgebraicSegmentSample.sample model root (prepare model root env) 8 H K bits

theorem every_path (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j)) (g : ThreeGeometry)
    (he : PlayerSpecificAlgebraicExpression.realEnv env x=RealThreeGeometryCode.environment g)
    (H K : ℕ) (bits : Fin (8*H+K) → Bool) :
    FullBudget g.budget (values (draw model root env H K bits) x) ∧
      InBox ![g.a,g.d,g.c] (values (draw model root env H K bits) x) := by
  have hf:=fields model root env hm hirr hv x hx hEnv g he
  have hP : ∀ slot,values ((prepare model root env).first.read slot) x=g.vertex (RationalThreeGeometry.edges slot).1 := by
    intro slot; funext j; exact hf.2.1 slot j
  have hQ : ∀ slot,values ((prepare model root env).second.read slot) x=g.vertex (RationalThreeGeometry.edges slot).2 := by
    intro slot; funext j; exact hf.2.2 slot j
  constructor
  · apply PlayerSpecificAlgebraicSegmentSample.budget model root (prepare model root env) 8 H K bits x g.budget hx.1
    · intro slot; rw [hP]; exact g.vertex_fullBudget _
    · intro slot; rw [hQ]; exact g.vertex_fullBudget _
  · apply PlayerSpecificAlgebraicSegmentSample.box model root (prepare model root env) 8 H K bits x ![g.a,g.d,g.c] hx.1
    · intro slot; rw [hP]; exact g.vertex_inBox _
    · intro slot; rw [hQ]; exact g.vertex_inBox _

theorem reduced (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data) (H K : ℕ)
    (bits : Fin (8*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) :
    ∀ j,Reduced root.polynomial ((draw model root env H K bits).read j) := by
  intro j
  unfold draw PlayerSpecificAlgebraicSegmentSample.sample interpolate
  rw [FixedArrayTable.read_ofFn]
  exact PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0

theorem random_bit_budget (H K : ℕ) : 8*H+K≤1000*H+2*K := by omega

end Blotto.PlayerSpecificAlgebraicThreeGeometrySample
