import Blotto.PlayerSpecificCachedOverlapRowPrograms

/-! Cached weight/test/endpoint rows have heights derived from the
original sixteen rows and the same fixed native syntax depths. -/
namespace Blotto.PlayerSpecificCachedOverlapRowBounds
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem atom (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) (e : RationalExpression 16) (H D : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H)
    (hl : e.LiteralHeights 2) (hd : e.depth≤D) :
    Reduced root.polynomial (PlayerSpecificAlgebraicExpression.run model root env e) ∧
      HasHeight (PlayerSpecificAlgebraicExpression.run model root env e) (iterate (D+1) H) := by
  have hr:=PlayerSpecificAlgebraicExpression.reduced model root env e hm hm0 (fun j => (hEnv j).1)
  have hh:=PlayerSpecificAlgebraicExpressionHeights.run_height model root env e hm hm0 hml H hmH (by omega) hEnv (e.LiteralHeights_mono hH hl)
  exact ⟨hr,mono hh (PlayerSpecificAlgebraicExpressionBudget.depth_mono H hd)⟩

theorem weight (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    Reduced root.polynomial (PlayerSpecificAlgebraicExpression.run model root env OverlapFormulaCode.weight) ∧
      HasHeight (PlayerSpecificAlgebraicExpression.run model root env OverlapFormulaCode.weight) (iterate 8 H) :=
  atom model root env OverlapFormulaCode.weight H 7 hm hm0 hml hmH hH hEnv OverlapFormulaCode.weight_literals OverlapFormulaCode.weight_depth

theorem fields_property (r : Data×(FixedArrayTable 4 Data×FixedArrayTable 4 Data)) (P : Data → Prop)
    (hw : P r.1) (hp : ∀ j,P (r.2.1.read j)) (hq : ∀ j,P (r.2.2.read j)) :
    ∀ j,P ((PlayerSpecificCachedOverlapRowExecution.fields r).read j) := by
  intro j
  fin_cases j
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hw
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hp 0
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hp 1
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hp 2
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hp 3
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hq 0
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hq 1
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hq 2
  · simpa [PlayerSpecificCachedOverlapRowExecution.fields,FixedArrayTable.read_ofFn] using hq 3

theorem fields (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    ∀ j,Reduced root.polynomial ((PlayerSpecificCachedOverlapRowExecution.fields (PlayerSpecificCachedOverlapRowExecution.run model root env).1).read j) ∧
      HasHeight ((PlayerSpecificCachedOverlapRowExecution.fields (PlayerSpecificCachedOverlapRowExecution.run model root env).1).read j) (iterate 10 H) := by
  rw [PlayerSpecificCachedOverlapRowExecution.value]
  apply fields_property _ (fun row => Reduced root.polynomial row ∧ HasHeight row (iterate 10 H))
  · have hw:=weight model root env H hm hm0 hml hmH hH hEnv
    exact ⟨hw.1,mono hw.2 (PlayerSpecificAlgebraicExpressionBudget.fuel_mono H (by decide : 8≤10))⟩
  · intro j
    simp only [PlayerSpecificAlgebraicOverlapTable.row,FixedArrayTable.read_ofFn]
    exact atom model root env (OverlapFormulaCode.safeP j) H 9 hm hm0 hml hmH hH hEnv (OverlapFormulaCode.safeP_literals j) (OverlapFormulaCode.safeP_depth j)
  · intro j
    simp only [PlayerSpecificAlgebraicOverlapTable.row,FixedArrayTable.read_ofFn]
    exact atom model root env (OverlapFormulaCode.safeQ j) H 9 hm hm0 hml hmH hH hEnv (OverlapFormulaCode.safeQ_literals j) (OverlapFormulaCode.safeQ_depth j)

theorem frame_cost (root : Candidate) (env : FixedArrayTable 16 Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H) (hH : 2≤H)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H) :
    price RationalCostModel.schoolbook (PlayerSpecificExpressionVectorExecution.frame root env
      (PlayerSpecificCachedOverlapRowExecution.fields (PlayerSpecificCachedOverlapRowExecution.run RationalCostModel.schoolbook root env).1))≤
        (5200*PlayerSpecificResourceCostProfile.rationalCoefficient)*(iterate 10 H+21)^3 := by
  let model:=RationalCostModel.schoolbook
  let S:=iterate 10 H+20
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 10 H
  have hHS : H≤S := by dsimp [S]; omega
  have hout:=fields model root env H hm hm0 hml hmH hH hEnv
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root env
    (PlayerSpecificCachedOverlapRowExecution.fields (PlayerSpecificCachedOverlapRowExecution.run model root env).1) S
    (mono hmH hHS) hml (mono he hHS)
    (fun j => ⟨mono (hEnv j).2 hHS,by have h:=(hEnv j).1.2; omega⟩)
    (fun j => ⟨mono (hout j).2 (by dsimp [S]; omega),by have h:=(hout j).1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 5200 S)
  rw [show S+1=iterate 10 H+21 by rfl] at hf'
  exact hf'

end Blotto.PlayerSpecificCachedOverlapRowBounds
