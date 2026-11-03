import Blotto.GeneralPaperExpressionMatrixLifetime

/-! Completed scalar rows and matrices retain their actual payload and
returned work/control records. The shared environment is owned exactly once;
surrounding already-completed arrays are passed through borrowed. -/
namespace Blotto.GeneralPaperExpressionArrayReturns
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEncodedScalarStorage (fields fields_bound natBits)
open GeneralPaperExpressionRowLifetime (rowTime)
open GeneralPaperExpressionMatrixLifetime (matrix matrixTime callback outerFoot outerProfile)
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem fields_mono_cap (A F : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ F) :
    fields A xs ≤ xs.length * (natBits F + A) + 32 * A :=
  fields_bound A (natBits F) xs (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (h x hx)) 1)

def rowWindow {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) (borrowed : ℕ) : ℕ :=
  let actual := GeneralPaperSegmentExpressionCompiler.row model A env programs
  borrowed + arrayFootprint A rationalWordWidth env + arrayFootprint A rationalWordWidth actual.1 +
    fields A [actual.2, 32 * A, actual.2 + 32 * A + 32] + 64 * A

def rowProfile (model : RationalCostModel) (A n k s d M borrowed : ℕ) : ℕ :=
  borrowed + arrayProfile A k (1 + 2 * s) + arrayProfile A n (1 + 2 * expressionHeightBudget s d) +
    3 * (natBits (rowTime model A n k s d M + 32 * A + 32) + A) + 96 * A

theorem row_return {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ j, (programs j).LiteralHeights s)
    (hd : ∀ j, (programs j).depth ≤ d) (hM : ∀ j, (programs j).operationBound ≤ M)
    (borrowed : ℕ) : rowWindow model A env programs borrowed ≤ rowProfile model A n k s d M borrowed := by
  have hEnvFoot := array_bound A (1 + 2 * s) rationalWordWidth env
    (fun j => rationalWordWidth_of_height (hEnv j))
  have hPayload := GeneralPaperExpressionMatrixLifetime.row_payload model A env programs s d hEnv hLit hd
  have hCost := GeneralPaperSegmentExpressionCompiler.row_work model A env programs
    (GeneralPaperExpressionRowLifetime.callbackTime model A k s d M)
    (fun j => GeneralPaperExpressionBitExecution.work_height model A env (programs j) s d M hEnv (hLit j) (hd j) (hM j))
  change (GeneralPaperSegmentExpressionCompiler.row model A env programs).2 ≤ rowTime model A n k s d M at hCost
  have hFields := fields_mono_cap A (rowTime model A n k s d M + 32 * A + 32)
    [(GeneralPaperSegmentExpressionCompiler.row model A env programs).2, 32 * A,
      (GeneralPaperSegmentExpressionCompiler.row model A env programs).2 + 32 * A + 32] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 3 * (natBits (rowTime model A n k s d M + 32 * A + 32) + A) + 32 * A at hFields
  unfold rowWindow rowProfile
  dsimp only
  omega

def outerRowWindow {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (i : Fin r) (borrowed : ℕ) : ℕ :=
  rowWindow model A env (programs i) (borrowed + outerFoot model A env programs i.val i.isLt.le)

theorem outer_row_return {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ i j, (programs i j).LiteralHeights s)
    (hd : ∀ i j, (programs i j).depth ≤ d) (hM : ∀ i j, (programs i j).operationBound ≤ M)
    (i : Fin r) (borrowed : ℕ) :
    outerRowWindow model A env programs i borrowed ≤
      rowProfile model A n k s d M (borrowed + outerProfile model A n r k s d M) := by
  have hRow := row_return model A env (programs i) s d M hEnv (hLit i) (hd i) (hM i)
    (borrowed + outerFoot model A env programs i.val i.isLt.le)
  have hOuter := GeneralPaperExpressionMatrixLifetime.outer_bound model A env programs s d M hEnv hLit hd hM i.val i.isLt.le
  unfold outerRowWindow
  apply hRow.trans
  unfold rowProfile
  omega

theorem matrix_payload {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (s d : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ i j, (programs i j).LiteralHeights s)
    (hd : ∀ i j, (programs i j).depth ≤ d) :
    arrayFootprint A (arrayFootprint A rationalWordWidth) (matrix model A env programs).1 ≤
      arrayProfile A r (arrayProfile A n (1 + 2 * expressionHeightBudget s d)) := by
  apply array_bound A _ (arrayFootprint A rationalWordWidth) _
  intro i
  rw [matrix, PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
  exact GeneralPaperExpressionMatrixLifetime.row_payload model A env (programs i) s d hEnv (hLit i) (hd i)

def matrixWindow {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (borrowed : ℕ) : ℕ :=
  let actual := matrix model A env programs
  borrowed + arrayFootprint A rationalWordWidth env + arrayFootprint A (arrayFootprint A rationalWordWidth) actual.1 +
    fields A [actual.2] + 64 * A

def matrixProfile (model : RationalCostModel) (A n r k s d M borrowed : ℕ) : ℕ :=
  borrowed + arrayProfile A k (1 + 2 * s) + arrayProfile A r (arrayProfile A n (1 + 2 * expressionHeightBudget s d)) +
    (natBits (matrixTime model A n r k s d M) + A) + 96 * A

theorem matrix_return {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ i j, (programs i j).LiteralHeights s)
    (hd : ∀ i j, (programs i j).depth ≤ d) (hM : ∀ i j, (programs i j).operationBound ≤ M)
    (borrowed : ℕ) : matrixWindow model A env programs borrowed ≤ matrixProfile model A n r k s d M borrowed := by
  have hEnvFoot := array_bound A (1 + 2 * s) rationalWordWidth env
    (fun j => rationalWordWidth_of_height (hEnv j))
  have hPayload := matrix_payload model A env programs s d hEnv hLit hd
  have hCost := GeneralPaperExpressionMatrixLifetime.work model A env programs s d M hEnv hLit hd hM
  have hFields := fields_mono_cap A (matrixTime model A n r k s d M) [(matrix model A env programs).2] (by
    intro x hx
    have he := List.mem_singleton.mp hx
    rw [he]
    exact hCost)
  simp only [List.length_singleton, one_mul] at hFields
  unfold matrixWindow matrixProfile
  dsimp only
  omega

end Blotto.GeneralPaperExpressionArrayReturns
