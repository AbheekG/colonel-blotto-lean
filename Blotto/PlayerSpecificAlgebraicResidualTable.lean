import Blotto.PlayerSpecificAlgebraicResidualEnvironment

/-! Actual three-slot residual weight/vertex code over algebraic rows.
Its exact finite-law reference is the already checked residual lottery. -/
namespace Blotto.PlayerSpecificAlgebraicResidualTable
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 3 :=
  let env:=PlayerSpecificAlgebraicResidualEnvironment.environment root a
  ⟨FixedArrayTable.ofFn (fun slot => PlayerSpecificAlgebraicExpression.run model root env (RationalNestedResidualCode.weights slot)),
    FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env
      (RationalNestedResidualCode.vertices (RationalNestedResidual.edges slot).1 j))),
    FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env
      (RationalNestedResidualCode.vertices (RationalNestedResidual.edges slot).2 j)))⟩

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (hvt : i.v< i.t) (htu : i.t< i.u) :
    Refines (prepare model root a) x (i.residualInput hvt htu).segmentLottery := by
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hb:=PlayerSpecificAlgebraicResidualEnvironment.bounds root a T hfit hm hm0 hml hmT
  have he:=PlayerSpecificAlgebraicResidualEnvironment.value root a i x hx.1 ha hvt htu
  have edges : RationalNestedResidual.edges=NestedResidual.edges := rfl
  constructor
  · intro slot
    simp only [prepare,FixedArrayTable.read_ofFn]
    rw [PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx (fun j => (hb j).1),he]
    exact RealNestedResidualCode.weight_value _ slot
  · intro slot
    funext j
    simp only [prepare,values,FixedArrayTable.read_ofFn]
    rw [PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx (fun j => (hb j).1),he]
    simpa only [NestedResidual.segmentLottery,edges] using RealNestedResidualCode.vertex_value (i.residualInput hvt htu)
      (RationalNestedResidual.edges slot).1 j
  · intro slot
    funext j
    simp only [prepare,values,FixedArrayTable.read_ofFn]
    rw [PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx (fun j => (hb j).1),he]
    simpa only [NestedResidual.segmentLottery,edges] using RealNestedResidualCode.vertex_value (i.residualInput hvt htu)
      (RationalNestedResidual.edges slot).2 j

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (hfit : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) : Bounds root (prepare model root a) (iterate 11 T) := by
  let env:=PlayerSpecificAlgebraicResidualEnvironment.environment root a
  have hb:=PlayerSpecificAlgebraicResidualEnvironment.bounds root a T hfit hm hm0 hml hmT
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 2 T
  have hrun : ∀ e : RationalExpression 5,e.LiteralHeights 2 → e.depth≤8 →
      Reduced root.polynomial (PlayerSpecificAlgebraicExpression.run model root env e) ∧
      HasHeight (PlayerSpecificAlgebraicExpression.run model root env e) (iterate 11 T) := by
    intro e hl hd
    have hr:=PlayerSpecificAlgebraicExpression.reduced model root env e hm hm0 (fun j => (hb j).1)
    have hh:=PlayerSpecificAlgebraicExpressionHeights.run_height model root env e hm hm0 hml (iterate 2 T)
      (mono hmT hbase) ((show 1≤T by omega).trans hbase) hb (e.LiteralHeights_mono (hT.trans hbase) hl)
    have hh':=mono hh (PlayerSpecificAlgebraicExpressionBudget.depth_mono (iterate 2 T) hd)
    rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hh'
    exact ⟨hr,hh'⟩
  constructor
  · intro slot
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact hrun _ (RationalNestedResidualCode.weight_literals slot) (RationalNestedResidualCode.weight_depth slot)
  · intro slot j
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact hrun _ (RationalNestedResidualCode.vertex_literals _ j) ((RationalNestedResidualCode.vertex_depth _ j).trans (by decide : 3≤8))
  · intro slot j
    simp only [prepare,FixedArrayTable.read_ofFn]
    exact hrun _ (RationalNestedResidualCode.vertex_literals _ j) ((RationalNestedResidualCode.vertex_depth _ j).trans (by decide : 3≤8))

end Blotto.PlayerSpecificAlgebraicResidualTable
