import Blotto.PlayerSpecificExpressionVectorFrameCost

/-! Complete finite local-program table work, including every executed
program, cached table, index traversal and returned coefficient array.
All intermediate row envelopes are derived from syntax depth and inputs. -/
namespace Blotto.PlayerSpecificExpressionVectorSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (H k m D : ℕ) : ℕ := PlayerSpecificAlgebraicExpressionFixedCost.size (H+m) k D

theorem lower (H k m D : ℕ) : H≤size H k m D ∧ k≤size H k m D ∧ m≤size H k m D ∧ 1≤size H k m D := by
  have h:=PlayerSpecificAlgebraicExpressionFixedCost.lower (H+m) k D
  dsimp only [size]
  omega

theorem frame_profile (A S R n : ℕ) : 200*n*R≤n*((A+8000001000)*(S+1)*R) := by
  nlinarith only [Nat.zero_le (n*A*(S+1)*R),Nat.zero_le (n*S*R),Nat.zero_le (n*R)]

theorem heights {k m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (program : FixedArrayTable m (RationalExpression k)) (H D : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H)
    (hDepth : ∀ j,(program.read j).depth≤D) (hLit : ∀ j,(program.read j).LiteralHeights H) :
    ∀ j,Reduced root.polynomial ((PlayerSpecificExpressionVectorExecution.run model root env program).1.read j) ∧
      HasHeight ((PlayerSpecificExpressionVectorExecution.run model root env program).1.read j) (size H k m D) := by
  let U:=H+m+k+10
  have hHU : H≤U := by dsimp [U]; omega
  intro j
  rw [PlayerSpecificExpressionVectorExecution.read_value]
  refine ⟨PlayerSpecificAlgebraicExpression.reduced model root env (program.read j) hm hm0 (fun j => (hEnv j).1),?_⟩
  have hn:=PlayerSpecificAlgebraicExpressionNodes.heights model root env (program.read j) hm hm0 hml U D (mono hmH hHU)
    (by dsimp [U]; omega) (fun j => ⟨(hEnv j).1,mono (hEnv j).2 hHU⟩) ((program.read j).LiteralHeights_mono hHU (hLit j)) (hDepth j)
  exact PlayerSpecificAlgebraicExpressionNodes.head _ _ hn

theorem cost {k m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (program : FixedArrayTable m (RationalExpression k)) (H D : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H)
    (hDepth : ∀ j,(program.read j).depth≤D) (hLit : ∀ j,(program.read j).LiteralHeights H) :
    (PlayerSpecificExpressionVectorExecution.run model root env program).2≤
      (PlayerSpecificExpressionVectorExecution.operations program+k+m+1)*PlayerSpecificAlgebraicExpressionPrimitiveCost.work model (size H k m D) := by
  let S:=size H k m D
  let W:=PlayerSpecificAlgebraicExpressionPrimitiveCost.work model S
  have hlow:=lower H k m D
  have hbody : (∑ j : Fin m,(PlayerSpecificAlgebraicExpressionExecution.run model root env (program.read j)).2)≤
      PlayerSpecificExpressionVectorExecution.operations program*W := by
    have hb : ∀ j : Fin m,(PlayerSpecificAlgebraicExpressionExecution.run model root env (program.read j)).2≤(program.read j).operationBound*W := by
      intro j
      exact PlayerSpecificAlgebraicExpressionFixedCost.input_cost model root env (program.read j) (H+m) D (hDepth j)
        hm hm0 hml (mono hmH (by omega)) (mono he (by omega)) hv
        (fun j => ⟨(hEnv j).1,mono (hEnv j).2 (by omega)⟩) ((program.read j).LiteralHeights_mono (by omega) (hLit j))
    have hb':=Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
    simpa only [PlayerSpecificExpressionVectorExecution.operations,Finset.sum_mul] using hb'
  have houtputs:=heights model root env program H D hm hm0 hml hmH hEnv hDepth hLit
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root env (PlayerSpecificExpressionVectorExecution.run model root env program).1 S
    (mono hmH hlow.1) hml (mono he hlow.1)
    (fun j => ⟨mono (hEnv j).2 hlow.1,by have h:=(hEnv j).1.2; omega⟩)
    (fun j => ⟨(houtputs j).2,by have h:=(houtputs j).1.2; omega⟩) hlow.2.1 hlow.2.2.1 hlow.2.2.2
  have hf':=hf.trans (frame_profile PlayerSpecificAlgebraicComparisonExecution.coefficient S
    (model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)) (k+m+1))
  change price model (PlayerSpecificExpressionVectorExecution.frame root env
    (PlayerSpecificExpressionVectorExecution.run model root env program).1)≤(k+m+1)*W at hf'
  rw [PlayerSpecificExpressionVectorExecution.price_equation]
  have hsum:=Nat.add_le_add hbody hf'
  apply hsum.trans_eq
  change _=(PlayerSpecificExpressionVectorExecution.operations program+k+m+1)*W
  ring

theorem polynomial_cost {k m : ℕ} (root : Candidate) (env : FixedArrayTable k Data)
    (program : FixedArrayTable m (RationalExpression k)) (H D : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) H)
    (hDepth : ∀ j,(program.read j).depth≤D) (hLit : ∀ j,(program.read j).LiteralHeights H) :
    (PlayerSpecificExpressionVectorExecution.run RationalCostModel.schoolbook root env program).2≤
      (PlayerSpecificExpressionVectorExecution.operations program+k+m+1)*
        PlayerSpecificAlgebraicExpressionFixedCost.polynomialCoefficient D*(H+m+k+11)^3 := by
  let n:=PlayerSpecificExpressionVectorExecution.operations program+k+m+1
  have hc:=cost RationalCostModel.schoolbook root env program H D hm hm0 hml hmH he hv hEnv hDepth hLit
  have hp:=PlayerSpecificAlgebraicExpressionFixedCost.calibrate n PlayerSpecificAlgebraicExpressionPrimitiveCost.coefficient (size H k m D) _ _
    (PlayerSpecificResourceCostProfile.cubic _ (size H k m D))
  exact (hc.trans hp).trans (PlayerSpecificAlgebraicExpressionFixedCost.transfer n _ _ _ _
    (PlayerSpecificAlgebraicExpressionFixedCost.size_linear (H+m) k D))

end Blotto.PlayerSpecificExpressionVectorSourceCost
