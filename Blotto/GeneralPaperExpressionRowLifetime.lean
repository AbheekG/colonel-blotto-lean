import Blotto.GeneralPaperNativeSegmentCallbackStorage

/-! Actual scalar-expression row construction, with one retained environment,
partial output, pending array frames and the executed expression's recursive
live scratch. Fixed code and other retained owners belong to borrowed. -/
namespace Blotto.GeneralPaperExpressionRowLifetime
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperIndexedArrayLifetime (window frame)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def callbackTime (model : RationalCostModel) (A k s d M : ℕ) : ℕ :=
  M * GeneralPaperExpressionBitExecution.nodeBound model A k (expressionHeightBudget s d)

def rowTime (model : RationalCostModel) (A n k s d M : ℕ) : ℕ :=
  n * callbackTime model A k s d M + PaperIndexedArrayConstruction.overhead id A n n

def sourceWindow {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) (i : ℕ) (hi : i < n) (borrowed : ℕ) : ℕ :=
  window id A (fun j => GeneralPaperExpressionBitExecution.run model A env (programs j)) rationalWordWidth i hi.le
    (borrowed + arrayFootprint A rationalWordWidth env)
    (GeneralPaperExpressionCallLifetime.live model A env (programs ⟨i, hi⟩))

def profile (model : RationalCostModel) (A n k s d M borrowed : ℕ) : ℕ :=
  borrowed + arrayProfile A k (1 + 2 * s) + arrayProfile A n (1 + 2 * expressionHeightBudget s d) +
    (n + 1) * frame A n (rowTime model A n k s d M) + 2048 * M * callbackTime model A k s d M

theorem actual {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ j, (programs j).LiteralHeights s)
    (hd : ∀ j, (programs j).depth ≤ d) (hM : ∀ j, (programs j).operationBound ≤ M)
    (i : ℕ) (hi : i < n) (borrowed : ℕ) :
    sourceWindow model A env programs i hi borrowed ≤ profile model A n k s d M borrowed := by
  have hEnvFoot := array_bound A (1 + 2 * s) rationalWordWidth env
    (fun j => rationalWordWidth_of_height (hEnv j))
  have hOutput : ∀ j, rationalWordWidth (GeneralPaperExpressionBitExecution.run model A env (programs j)).1 ≤
      1 + 2 * expressionHeightBudget s d := by
    intro j
    rw [GeneralPaperExpressionBitExecution.data]
    exact rationalWordWidth_of_height (((programs j).run_height env s hEnv (hLit j)).mono
      (expressionHeightBudget_mono s (hd j)))
  have hScratch := GeneralPaperExpressionCallLifetime.height_bound model A env (programs ⟨i, hi⟩) s d M hEnv
    (hLit _) (hd _) (hM _)
  have hWindow := GeneralPaperIndexedArrayLifetime.window_bound id A
    (fun j => GeneralPaperExpressionBitExecution.run model A env (programs j)) rationalWordWidth
    (1 + 2 * expressionHeightBudget s d) (2048 * M * callbackTime model A k s d M) hOutput i hi.le
    (borrowed + arrayFootprint A rationalWordWidth env) _ hScratch
  have hCost : (PaperIndexedArrayConstruction.run id A
      (fun j => GeneralPaperExpressionBitExecution.run model A env (programs j))).2 ≤ rowTime model A n k s d M :=
    GeneralPaperSegmentExpressionCompiler.row_work model A env programs (callbackTime model A k s d M)
      (fun j => GeneralPaperExpressionBitExecution.work_height model A env (programs j) s d M hEnv (hLit j) (hd j) (hM j))
  have hFrame := GeneralPaperIndexedArrayLifetime.frame_mono A n _ _ hCost
  unfold sourceWindow profile
  exact hWindow.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left hEnvFoot borrowed)
      (arrayProfile A n (1 + 2 * expressionHeightBudget s d)))
      (Nat.mul_le_mul_left (n + 1) hFrame)) _)

@[fun_prop]
theorem node_scale (model : RationalCostModel) (k s : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun A => GeneralPaperExpressionBitExecution.nodeBound model A k s) := by
  unfold GeneralPaperExpressionBitExecution.nodeBound GeneralPaperExpressionBitExecution.unit
  fun_prop

@[fun_prop]
theorem time_scale (model : RationalCostModel) (n k s d M : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun A => rowTime model A n k s d M) := by
  unfold rowTime callbackTime
  fun_prop

theorem profile_scale (model : RationalCostModel) (n k s d M : ℕ) (borrowed : ℕ → ℕ)
    (hb : GeneralPaperReferenceScaling.Scale borrowed) :
    GeneralPaperReferenceScaling.Scale (fun A => profile model A n k s d M (borrowed A)) := by
  unfold profile callbackTime GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

end Blotto.GeneralPaperExpressionRowLifetime
