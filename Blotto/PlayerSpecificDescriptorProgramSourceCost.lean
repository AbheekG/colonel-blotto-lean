import Blotto.PlayerSpecificDescriptorProgramFrameCost

/-! A complete measured local segment table has polynomial source
work from input heights and fixed local syntax depth. All produced row
sizes are derived internally; no real interpretation is needed. -/
namespace Blotto.PlayerSpecificDescriptorProgramSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (H k n m D : ℕ) : ℕ := PlayerSpecificAlgebraicExpressionFixedCost.size (H+m+n) k D

theorem lower (H k n m D : ℕ) : H≤size H k n m D ∧ k≤size H k n m D ∧ n≤size H k n m D ∧ m≤size H k n m D ∧ 1≤size H k n m D := by
  have h:=PlayerSpecificAlgebraicExpressionFixedCost.lower (H+m+n) k D
  dsimp only [size]
  omega

theorem frame_profile (A S R t : ℕ) : 1000*t*R≤t*((A+8000001000)*(S+1)*R) := by
  nlinarith only [Nat.zero_le (t*A*(S+1)*R),Nat.zero_le (t*S*R),Nat.zero_le (t*R)]

theorem cost {k n m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (weights : FixedArrayTable m (RationalExpression k))
    (first second : FixedArrayTable m (FixedArrayTable n (RationalExpression k))) (H D : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H)
    (hw : ∀ slot,(weights.read slot).depth≤D ∧ (weights.read slot).LiteralHeights H)
    (hp : ∀ slot j,((first.read slot).read j).depth≤D ∧ ((first.read slot).read j).LiteralHeights H)
    (hq : ∀ slot j,((second.read slot).read j).depth≤D ∧ ((second.read slot).read j).LiteralHeights H) :
    (PlayerSpecificDescriptorProgramExecution.run model root env weights first second).2≤
      (PlayerSpecificDescriptorProgramExecution.operations weights first second+k+m*(2*n+1)+1)*
        PlayerSpecificAlgebraicExpressionPrimitiveCost.work model (size H k n m D) := by
  let S:=size H k n m D
  let W:=PlayerSpecificAlgebraicExpressionPrimitiveCost.work model S
  let result:=(PlayerSpecificDescriptorProgramExecution.run model root env weights first second).1
  have hlow:=lower H k n m D
  have hsource : ∀ e : RationalExpression k,e.depth≤D → e.LiteralHeights H →
      (PlayerSpecificAlgebraicExpressionExecution.run model root env e).2≤e.operationBound*W := by
    intro e hd hl
    exact PlayerSpecificAlgebraicExpressionFixedCost.input_cost model root env e (H+m+n) D hd hm hm0 hml
      (mono hmH (by omega)) (mono he (by omega)) hv (fun j => ⟨(hEnv j).1,mono (hEnv j).2 (by omega)⟩)
      (e.LiteralHeights_mono (by omega) hl)
  have hrow : ∀ e : RationalExpression k,e.depth≤D → e.LiteralHeights H →
      HasHeight (PlayerSpecificAlgebraicExpression.run model root env e) S ∧
      (PlayerSpecificAlgebraicExpression.run model root env e).length≤3 := by
    intro e hd hl
    have hr:=PlayerSpecificAlgebraicExpression.reduced model root env e hm hm0 (fun j => (hEnv j).1)
    have hn:=PlayerSpecificAlgebraicExpressionNodes.heights model root env e hm hm0 hml (H+m+n+k+10) D
      (mono hmH (by omega)) (by omega) (fun j => ⟨(hEnv j).1,mono (hEnv j).2 (by omega)⟩)
      (e.LiteralHeights_mono (by omega) hl) hd
    exact ⟨PlayerSpecificAlgebraicExpressionNodes.head _ _ hn,by have h:=hr.2; omega⟩
  have hrows : ∀ row∈PlayerSpecificDescriptorProgramExecution.rows result,HasHeight row S ∧ row.length≤3 := by
    refine PlayerSpecificDescriptorProgramFrameCost.rows_property result (fun row => HasHeight row S ∧ row.length≤3) ?_ ?_ ?_
    · intro slot
      dsimp only [result]
      rw [PlayerSpecificDescriptorProgramExecution.value,FixedArrayTable.read_ofFn]
      exact hrow _ (hw slot).1 (hw slot).2
    · intro slot j
      dsimp only [result]
      rw [PlayerSpecificDescriptorProgramExecution.value,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
      exact hrow _ (hp slot j).1 (hp slot j).2
    · intro slot j
      dsimp only [result]
      rw [PlayerSpecificDescriptorProgramExecution.value,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
      exact hrow _ (hq slot j).1 (hq slot j).2
  have hf:=PlayerSpecificDescriptorProgramFrameCost.cost model root env result S (mono hmH hlow.1) hml (mono he hlow.1)
    (fun j => ⟨mono (hEnv j).2 hlow.1,by have h:=(hEnv j).1.2; omega⟩) hrows
    hlow.2.1 hlow.2.2.1 hlow.2.2.2.1 hlow.2.2.2.2
  have hf':=hf.trans (frame_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S
    (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)) (k+m*(2*n+1)+1))
  change price model (PlayerSpecificDescriptorProgramExecution.frame root env result)≤(k+m*(2*n+1)+1)*W at hf'
  have hw':=Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) => hsource _ (hw slot).1 (hw slot).2)
  have hp':=Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hsource _ (hp slot j).1 (hp slot j).2))
  have hq':=Finset.sum_le_sum (fun slot (_ : slot∈Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hsource _ (hq slot j).1 (hq slot j).2))
  have hbody:=Nat.add_le_add (Nat.add_le_add hw' hp') hq'
  have hbody' : (∑ slot : Fin m,(PlayerSpecificAlgebraicExpressionExecution.run model root env (weights.read slot)).2)+
      (∑ slot : Fin m,∑ j : Fin n,(PlayerSpecificAlgebraicExpressionExecution.run model root env ((first.read slot).read j)).2)+
      (∑ slot : Fin m,∑ j : Fin n,(PlayerSpecificAlgebraicExpressionExecution.run model root env ((second.read slot).read j)).2)≤
      PlayerSpecificDescriptorProgramExecution.operations weights first second*W := by
    simpa only [PlayerSpecificDescriptorProgramExecution.operations,Nat.add_mul,Finset.sum_mul] using hbody
  rw [PlayerSpecificDescriptorProgramExecution.price_equation]
  apply (Nat.add_le_add hbody' hf').trans_eq
  change _=(PlayerSpecificDescriptorProgramExecution.operations weights first second+k+m*(2*n+1)+1)*W
  ring

theorem polynomial_cost {k n m : ℕ} (root : Candidate) (env : FixedArrayTable k Data)
    (weights : FixedArrayTable m (RationalExpression k))
    (first second : FixedArrayTable m (FixedArrayTable n (RationalExpression k))) (H D : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H)
    (hw : ∀ slot,(weights.read slot).depth≤D ∧ (weights.read slot).LiteralHeights H)
    (hp : ∀ slot j,((first.read slot).read j).depth≤D ∧ ((first.read slot).read j).LiteralHeights H)
    (hq : ∀ slot j,((second.read slot).read j).depth≤D ∧ ((second.read slot).read j).LiteralHeights H) :
    (PlayerSpecificDescriptorProgramExecution.run RationalCostModel.schoolbook root env weights first second).2≤
      (PlayerSpecificDescriptorProgramExecution.operations weights first second+k+m*(2*n+1)+1)*
        PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient D*(H+m+n+k+11)^3 := by
  let t:=PlayerSpecificDescriptorProgramExecution.operations weights first second+k+m*(2*n+1)+1
  have hc:=cost RationalCostModel.schoolbook root env weights first second H D hm hm0 hml hmH he hv hEnv hw hp hq
  have hc':=PlayerSpecificAlgebraicExpressionFixedCost.calibrate t PlayerSpecificAlgebraicExpressionPrimitiveCost.coefficient (size H k n m D) _ _
    (PlayerSpecificResourceCostProfile.cubic _ (size H k n m D))
  exact (hc.trans hc').trans (PlayerSpecificAlgebraicExpressionFixedCost.transfer t _ _ _ _
    (PlayerSpecificAlgebraicExpressionFixedCost.size_linear (H+m+n) k D))

end Blotto.PlayerSpecificDescriptorProgramSourceCost
