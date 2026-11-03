import Blotto.GeneralPaperExpressionArrayReturns

/-! Retained owners and final descriptor assembly for the executed segment
compiler. Program/height hypotheses are erased mathematical certificates;
the measured producer remains unchanged. Environment/code construction is
outside this compiler and belongs to its calling factory. -/
namespace Blotto.GeneralPaperSegmentCompilerStorage
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperSegmentExpressionCompiler (Programs row)
open GeneralPaperExpressionMatrixLifetime (matrix matrixTime)
open GeneralPaperExpressionRowLifetime (rowTime callbackTime)
set_option autoImplicit false
set_option maxHeartbeats 1600000

structure Bounds {n r k : ℕ} {l : RationalSegmentLottery n r} {env : FixedArrayTable k ℚ}
    (p : Programs l env) (s d M : ℕ) : Prop where
  environment : ∀ j, RationalHeight (env.read j) s
  weight_literals : ∀ i, (p.weight i).LiteralHeights s
  left_literals : ∀ i j, (p.left i j).LiteralHeights s
  right_literals : ∀ i j, (p.right i j).LiteralHeights s
  weight_depth : ∀ i, (p.weight i).depth ≤ d
  left_depth : ∀ i j, (p.left i j).depth ≤ d
  right_depth : ∀ i j, (p.right i j).depth ≤ d
  weight_operations : ∀ i, (p.weight i).operationBound ≤ M
  left_operations : ∀ i j, (p.left i j).operationBound ≤ M
  right_operations : ∀ i j, (p.right i j).operationBound ≤ M

def owner {α : Type*} (A : ℕ) (encode : α → ℕ) (actual : α × ℕ) : ℕ :=
  encode actual.1 + natBits actual.2 + 64 * A

theorem owner_bound {α : Type*} (A P F : ℕ) (encode : α → ℕ) (actual : α × ℕ)
    (hP : encode actual.1 ≤ P) (hF : actual.2 ≤ F) :
    owner A encode actual ≤ P + natBits F + 64 * A := by
  have hBits := Nat.add_le_add_left (binaryWordWidth_mono hF) 1
  unfold owner natBits
  omega

def rowOwnerProfile (model : RationalCostModel) (A n k s d M : ℕ) : ℕ :=
  arrayProfile A n (1 + 2 * expressionHeightBudget s d) + natBits (rowTime model A n k s d M) + 64 * A

def matrixOwnerProfile (model : RationalCostModel) (A n r k s d M : ℕ) : ℕ :=
  arrayProfile A r (arrayProfile A n (1 + 2 * expressionHeightBudget s d)) +
    natBits (matrixTime model A n r k s d M) + 64 * A

theorem row_owner {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ j, (programs j).LiteralHeights s)
    (hd : ∀ j, (programs j).depth ≤ d) (hM : ∀ j, (programs j).operationBound ≤ M) :
    owner A (arrayFootprint A rationalWordWidth) (row model A env programs) ≤ rowOwnerProfile model A n k s d M :=
  owner_bound A _ _ _ _ (GeneralPaperExpressionMatrixLifetime.row_payload model A env programs s d hEnv hLit hd)
    (GeneralPaperSegmentExpressionCompiler.row_work model A env programs (callbackTime model A k s d M)
      (fun j => GeneralPaperExpressionBitExecution.work_height model A env (programs j) s d M hEnv (hLit j) (hd j) (hM j)))

theorem matrix_owner {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ i j, (programs i j).LiteralHeights s)
    (hd : ∀ i j, (programs i j).depth ≤ d) (hM : ∀ i j, (programs i j).operationBound ≤ M) :
    owner A (arrayFootprint A (arrayFootprint A rationalWordWidth)) (matrix model A env programs) ≤
      matrixOwnerProfile model A n r k s d M :=
  owner_bound A _ _ _ _ (GeneralPaperExpressionArrayReturns.matrix_payload model A env programs s d hEnv hLit hd)
    (GeneralPaperExpressionMatrixLifetime.work model A env programs s d M hEnv hLit hd hM)

def compilerTime (model : RationalCostModel) (A n r k s d M : ℕ) : ℕ :=
  GeneralPaperSegmentExpressionCompiler.bound A n r (callbackTime model A k s d M)

theorem compiler_work {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (p : Programs l env) (s d M : ℕ) (h : Bounds p s d M) :
    (GeneralPaperSegmentExpressionCompiler.run model A env p).2 ≤ compilerTime model A n r k s d M :=
  GeneralPaperSegmentExpressionCompiler.work model A env p (callbackTime model A k s d M)
    (fun i => GeneralPaperExpressionBitExecution.work_height model A env (p.weight i) s d M h.environment
      (h.weight_literals i) (h.weight_depth i) (h.weight_operations i))
    (fun i j => GeneralPaperExpressionBitExecution.work_height model A env (p.left i j) s d M h.environment
      (h.left_literals i j) (h.left_depth i j) (h.left_operations i j))
    (fun i j => GeneralPaperExpressionBitExecution.work_height model A env (p.right i j) s d M h.environment
      (h.right_literals i j) (h.right_depth i j) (h.right_operations i j))

def assemblyWindow {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (p : Programs l env) (borrowed : ℕ) : ℕ :=
  let w := row model A env p.weight
  let left := matrix model A env p.left
  let right := matrix model A env p.right
  let actual := GeneralPaperSegmentExpressionCompiler.run model A env p
  borrowed + arrayFootprint A rationalWordWidth env +
    arrayFootprint A rationalWordWidth actual.1.weights +
    arrayFootprint A (arrayFootprint A rationalWordWidth) actual.1.left +
    arrayFootprint A (arrayFootprint A rationalWordWidth) actual.1.right +
    fields A [w.2, left.2, right.2, w.2 + left.2, w.2 + left.2 + right.2, 64 * A, actual.2] + 128 * A

def assemblyProfile (model : RationalCostModel) (A n r k s d M borrowed : ℕ) : ℕ :=
  borrowed + arrayProfile A k (1 + 2 * s) + arrayProfile A r (1 + 2 * expressionHeightBudget s d) +
    2 * arrayProfile A r (arrayProfile A n (1 + 2 * expressionHeightBudget s d)) +
    7 * (natBits (compilerTime model A n r k s d M) + A) + 160 * A

theorem assembly {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (env : FixedArrayTable k ℚ) (p : Programs l env) (s d M : ℕ) (h : Bounds p s d M) (borrowed : ℕ) :
    assemblyWindow model A env p borrowed ≤ assemblyProfile model A n r k s d M borrowed := by
  let w := row model A env p.weight
  let left := matrix model A env p.left
  let right := matrix model A env p.right
  let actual := GeneralPaperSegmentExpressionCompiler.run model A env p
  have hEnv := array_bound A (1 + 2 * s) rationalWordWidth env (fun j => rationalWordWidth_of_height (h.environment j))
  have hW := GeneralPaperExpressionMatrixLifetime.row_payload model A env p.weight s d h.environment h.weight_literals h.weight_depth
  have hL := GeneralPaperExpressionArrayReturns.matrix_payload model A env p.left s d h.environment h.left_literals h.left_depth
  have hR := GeneralPaperExpressionArrayReturns.matrix_payload model A env p.right s d h.environment h.right_literals h.right_depth
  change arrayFootprint A rationalWordWidth w.1 ≤ _ at hW
  change arrayFootprint A (arrayFootprint A rationalWordWidth) left.1 ≤ _ at hL
  change arrayFootprint A (arrayFootprint A rationalWordWidth) right.1 ≤ _ at hR
  have hCost : actual.2 ≤ compilerTime model A n r k s d M := compiler_work model A env p s d M h
  have hTotal : actual.2 = w.2 + left.2 + right.2 + 64 * A + 64 := rfl
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (compilerTime model A n r k s d M)
    [w.2, left.2, right.2, w.2 + left.2, w.2 + left.2 + right.2, 64 * A, actual.2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 7 * (natBits (compilerTime model A n r k s d M) + A) + 32 * A at hFields
  change borrowed + arrayFootprint A rationalWordWidth env + arrayFootprint A rationalWordWidth w.1 +
    arrayFootprint A (arrayFootprint A rationalWordWidth) left.1 +
    arrayFootprint A (arrayFootprint A rationalWordWidth) right.1 +
    fields A [w.2, left.2, right.2, w.2 + left.2, w.2 + left.2 + right.2, 64 * A, actual.2] + 128 * A ≤ _
  unfold assemblyProfile
  omega

end Blotto.GeneralPaperSegmentCompilerStorage
