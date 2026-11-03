import Blotto.GeneralPaperExpressionRowLifetime

/-! Nested endpoint arrays retain completed rows while the next row executes.
The inner-row lifetime owns the shared environment once. Outer partial-array
payload, pending outer frames and callback-return controls are added here. -/
namespace Blotto.GeneralPaperExpressionMatrixLifetime
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperIndexedArrayLifetime (prefixTable activationFoot frame)
open GeneralPaperExpressionRowLifetime (rowTime)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def callback {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (i : Fin r) : FixedArrayTable n ℚ × ℕ :=
  let actual := GeneralPaperSegmentExpressionCompiler.row model A env (programs i)
  (actual.1, actual.2 + 32 * A + 32)

def matrix {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) :=
  PaperIndexedArrayConstruction.run id A (callback model A env programs)

def matrixTime (model : RationalCostModel) (A n r k s d M : ℕ) : ℕ :=
  r * (rowTime model A n k s d M + 32 * A + 32) + PaperIndexedArrayConstruction.overhead id A r r

theorem row_payload {n k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin n → RationalExpression k) (s d : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ j, (programs j).LiteralHeights s)
    (hd : ∀ j, (programs j).depth ≤ d) :
    arrayFootprint A rationalWordWidth (GeneralPaperSegmentExpressionCompiler.row model A env programs).1 ≤
      arrayProfile A n (1 + 2 * expressionHeightBudget s d) := by
  apply array_bound A _ rationalWordWidth _
  intro j
  rw [GeneralPaperSegmentExpressionCompiler.row_data, FixedArrayTable.read_ofFn]
  exact rationalWordWidth_of_height (((programs j).run_height env s hEnv (hLit j)).mono
    (expressionHeightBudget_mono s (hd j)))

theorem work {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ i j, (programs i j).LiteralHeights s)
    (hd : ∀ i j, (programs i j).depth ≤ d) (hM : ∀ i j, (programs i j).operationBound ≤ M) :
    (matrix model A env programs).2 ≤ matrixTime model A n r k s d M :=
  GeneralPaperSegmentExpressionCompiler.matrix_work model A env programs
    (GeneralPaperExpressionRowLifetime.callbackTime model A k s d M)
    (fun i j => GeneralPaperExpressionBitExecution.work_height model A env (programs i j) s d M
      hEnv (hLit i j) (hd i j) (hM i j))

def outerFoot {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (i : ℕ) (hi : i ≤ r) : ℕ :=
  arrayFootprint A (arrayFootprint A rationalWordWidth)
      (prefixTable id A (callback model A env programs) i hi) +
    activationFoot id A (callback model A env programs) i hi

def outerProfile (model : RationalCostModel) (A n r k s d M : ℕ) : ℕ :=
  arrayProfile A r (arrayProfile A n (1 + 2 * expressionHeightBudget s d)) +
    (r + 1) * frame A r (matrixTime model A n r k s d M)

theorem outer_bound {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ i j, (programs i j).LiteralHeights s)
    (hd : ∀ i j, (programs i j).depth ≤ d) (hM : ∀ i j, (programs i j).operationBound ≤ M)
    (i : ℕ) (hi : i ≤ r) : outerFoot model A env programs i hi ≤ outerProfile model A n r k s d M := by
  have hPrefix := GeneralPaperIndexedArrayLifetime.prefix_payload id A (callback model A env programs)
    (arrayFootprint A rationalWordWidth) (arrayProfile A n (1 + 2 * expressionHeightBudget s d))
    (fun j => row_payload model A env (programs j) s d hEnv (hLit j) (hd j)) i hi
  have hFrames := GeneralPaperIndexedArrayLifetime.activation_bound id A (callback model A env programs) i hi
  have hFrame := GeneralPaperIndexedArrayLifetime.frame_mono A r _ _
    (work model A env programs s d M hEnv hLit hd hM)
  exact Nat.add_le_add hPrefix (hFrames.trans (Nat.mul_le_mul_left (r + 1) hFrame))

def activeWindow {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (i : ℕ) (hi : i < r)
    (j : ℕ) (hj : j < n) (borrowed : ℕ) : ℕ :=
  GeneralPaperExpressionRowLifetime.sourceWindow model A env (programs ⟨i, hi⟩) j hj
    (borrowed + outerFoot model A env programs i hi.le)

def activeProfile (model : RationalCostModel) (A n r k s d M borrowed : ℕ) : ℕ :=
  GeneralPaperExpressionRowLifetime.profile model A n k s d M
    (borrowed + outerProfile model A n r k s d M)

theorem active {n r k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (programs : Fin r → Fin n → RationalExpression k) (s d M : ℕ)
    (hEnv : ∀ j, RationalHeight (env.read j) s) (hLit : ∀ i j, (programs i j).LiteralHeights s)
    (hd : ∀ i j, (programs i j).depth ≤ d) (hM : ∀ i j, (programs i j).operationBound ≤ M)
    (i : ℕ) (hi : i < r) (j : ℕ) (hj : j < n) (borrowed : ℕ) :
    activeWindow model A env programs i hi j hj borrowed ≤ activeProfile model A n r k s d M borrowed := by
  have hRow := GeneralPaperExpressionRowLifetime.actual model A env (programs ⟨i, hi⟩) s d M hEnv
    (hLit _) (hd _) (hM _) j hj (borrowed + outerFoot model A env programs i hi.le)
  have hOuter := outer_bound model A env programs s d M hEnv hLit hd hM i hi.le
  unfold activeWindow activeProfile
  apply hRow.trans
  unfold GeneralPaperExpressionRowLifetime.profile
  omega

end Blotto.GeneralPaperExpressionMatrixLifetime
