import Blotto.PlayerSpecificAlgebraicOverlapEnvironment

/-! Actual retained-field overlap descriptors cache one environment and
all three outputs per slot. Total divisions and safe fallbacks are exact. -/
namespace Blotto.PlayerSpecificAlgebraicOverlapTable
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificAlgebraicOverlapEnvironment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def row (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) :
    Data × (FixedArrayTable 4 Data × FixedArrayTable 4 Data) :=
  (PlayerSpecificAlgebraicExpression.run model root env OverlapFormulaCode.weight,
    FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env (OverlapFormulaCode.safeP j)),
    FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicExpression.run model root env (OverlapFormulaCode.safeQ j)))

def prepare {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) : Descriptor 4 (k*h) :=
  let rows := FixedArrayTable.ofFn (fun slot : Fin (k*h) =>
    let ij := finProdFinEquiv.symm slot
    row model root (environment first second interval budget ij.1 ij.2))
  ⟨FixedArrayTable.ofFn (fun slot => (rows.read slot).1),
    FixedArrayTable.ofFn (fun slot => (rows.read slot).2.1),FixedArrayTable.ofFn (fun slot => (rows.read slot).2.2)⟩

theorem refines {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (G : OverlapGluing k h) (B : ℝ) (hf : Refines first x G.first) (hs : Refines second x G.second)
    (hi : realEvaluate interval x=G.d) (hb : realEvaluate budget x=B)
    (hEnv : ∀ i j r,Reduced root.polynomial ((environment first second interval budget i j).read r))
    (hFirst : G.firstProbe=AffineProbe.coordinate 2) (hSecond : G.secondProbe=AffineProbe.reflectedCoordinate G.d 0) :
    Refines (prepare model root first second interval budget) x (G.descriptor B) := by
  constructor
  · intro slot
    simp only [prepare,row,FixedArrayTable.read_ofFn]
    rw [PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx (hEnv _ _),
      PlayerSpecificAlgebraicOverlapEnvironment.value first second interval budget x G B hf hs hi hb]
    exact RealOverlapFormula.weight_value G B _ _ hFirst hSecond
  · intro slot
    funext j
    simp only [prepare,row,values,FixedArrayTable.read_ofFn]
    rw [PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx (hEnv _ _),
      PlayerSpecificAlgebraicOverlapEnvironment.value first second interval budget x G B hf hs hi hb]
    exact RealOverlapFormula.safeP_value G B _ _ hFirst hSecond j
  · intro slot
    funext j
    simp only [prepare,row,values,FixedArrayTable.read_ofFn]
    rw [PlayerSpecificAlgebraicExpressionValue.value model root _ _ hm hirr hv x hx (hEnv _ _),
      PlayerSpecificAlgebraicOverlapEnvironment.value first second interval budget x G B hf hs hi hb]
    exact RealOverlapFormula.safeQ_value G B _ _ hFirst hSecond j

theorem bounds {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (T : ℕ) (hf : Bounds root first T) (hs : Bounds root second T)
    (hi : Reduced root.polynomial interval ∧ HasHeight interval T) (hb : Reduced root.polynomial budget ∧ HasHeight budget T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    Bounds root (prepare model root first second interval budget) (iterate 10 T) := by
  have he := PlayerSpecificAlgebraicOverlapEnvironment.bounds root first second interval budget T hf hs hi hb
  have hrun : ∀ (i : Fin k) (j : Fin h) (e : RationalExpression 16),e.LiteralHeights 2 → e.depth ≤ 9 →
      Reduced root.polynomial (PlayerSpecificAlgebraicExpression.run model root (environment first second interval budget i j) e) ∧
      HasHeight (PlayerSpecificAlgebraicExpression.run model root (environment first second interval budget i j) e) (iterate 10 T) := by
    intro i j e hl hd
    refine ⟨PlayerSpecificAlgebraicExpression.reduced model root _ e hm hm0 (fun r => (he i j r).1),?_⟩
    have hh := PlayerSpecificAlgebraicExpressionHeights.run_height model root _ e hm hm0 hml T hmT (by omega)
      (he i j) (e.LiteralHeights_mono hT hl)
    exact mono hh (PlayerSpecificAlgebraicExpressionBudget.depth_mono T hd)
  constructor
  · intro slot
    simp only [prepare,row,FixedArrayTable.read_ofFn]
    exact hrun _ _ _ OverlapFormulaCode.weight_literals (OverlapFormulaCode.weight_depth.trans (by omega : 7 ≤ 9))
  · intro slot j
    simp only [prepare,row,FixedArrayTable.read_ofFn]
    exact hrun _ _ _ (OverlapFormulaCode.safeP_literals j) (OverlapFormulaCode.safeP_depth j)
  · intro slot j
    simp only [prepare,row,FixedArrayTable.read_ofFn]
    exact hrun _ _ _ (OverlapFormulaCode.safeQ_literals j) (OverlapFormulaCode.safeQ_depth j)

end Blotto.PlayerSpecificAlgebraicOverlapTable
