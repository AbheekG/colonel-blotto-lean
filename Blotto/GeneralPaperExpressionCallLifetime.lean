import Blotto.GeneralPaperExpressionLocalStorage

/-! Recursive live-frame envelope for the executed fused evaluator. Parent
operands/results and localCost primitive scratch remain reserved during child
calls. The conditional follows only the reached continuation. Borrowed code
and the shared environment are accounted once by the caller. -/
namespace Blotto.GeneralPaperExpressionCallLifetime
open GeneralPaperExpressionBitExecution (run)
open GeneralPaperExpressionLocalStorage (localFoot)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def live {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ) : RationalExpression k → ℕ
  | .input j => localFoot model A env (.input j)
  | .literal q => localFoot model A env (.literal q)
  | .add a b => localFoot model A env (.add a b) + max (live model A env a) (live model A env b)
  | .sub a b => localFoot model A env (.sub a b) + max (live model A env a) (live model A env b)
  | .mul a b => localFoot model A env (.mul a b) + max (live model A env a) (live model A env b)
  | .div a b => localFoot model A env (.div a b) + max (live model A env a) (live model A env b)
  | .minimum a b => localFoot model A env (.minimum a b) + max (live model A env a) (live model A env b)
  | .maximum a b => localFoot model A env (.maximum a b) + max (live model A env a) (live model A env b)
  | .ifLe a b yes no => localFoot model A env (.ifLe a b yes no) +
      max (live model A env a) (max (live model A env b)
        (if (run model A env a).1 ≤ (run model A env b).1 then live model A env yes else live model A env no))

theorem join (a b c N F localCost p q r : ℕ)
    (hLocal : localCost ≤ 2048 * F) (hp : p ≤ 2048 * a * F) (hq : q ≤ 2048 * b * F)
    (hr : r ≤ 2048 * c * F) (hOps : a + b + c + 1 ≤ N) :
    localCost + max p (max q r) ≤ 2048 * N * F := by
  have hP := hp.trans (Nat.mul_le_mul_right F (Nat.mul_le_mul_left 2048 (show a ≤ a + b + c by omega)))
  have hQ := hq.trans (Nat.mul_le_mul_right F (Nat.mul_le_mul_left 2048 (show b ≤ a + b + c by omega)))
  have hR := hr.trans (Nat.mul_le_mul_right F (Nat.mul_le_mul_left 2048 (show c ≤ a + b + c by omega)))
  have hMax := max_le hP (max_le hQ hR)
  have hScale := Nat.mul_le_mul_right F (Nat.mul_le_mul_left 2048 hOps)
  nlinarith only [hLocal, hMax, hScale]

theorem bound {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ) (e : RationalExpression k) :
    live model A env e ≤ 2048 * e.operationBound * (run model A env e).2 := by
  induction e with
  | input j => simpa only [live, RationalExpression.operationBound, Nat.mul_one] using GeneralPaperExpressionLocalStorage.bound model A env (.input j)
  | literal q => simpa only [live, RationalExpression.operationBound, Nat.mul_one] using GeneralPaperExpressionLocalStorage.bound model A env (.literal q)
  | add a b ha hb =>
    have hLocal := GeneralPaperExpressionLocalStorage.bound model A env (.add a b)
    have hLeft : (run model A env a).2 ≤ (run model A env (.add a b)).2 := by rw [run]; dsimp only; omega
    have hRight : (run model A env b).2 ≤ (run model A env (.add a b)).2 := by rw [run]; dsimp only; omega
    have hA := ha.trans (Nat.mul_le_mul_left (2048 * a.operationBound) hLeft)
    have hB := hb.trans (Nat.mul_le_mul_left (2048 * b.operationBound) hRight)
    have h := join a.operationBound b.operationBound 0 (RationalExpression.operationBound (.add a b))
      (run model A env (.add a b)).2 (localFoot model A env (.add a b))
      (live model A env a) (live model A env b) 0 hLocal hA hB (by simp)
      (by simp only [RationalExpression.operationBound]; omega)
    simpa only [live, Nat.zero_mul, Nat.max_zero] using h
  | sub a b ha hb =>
    have hLocal := GeneralPaperExpressionLocalStorage.bound model A env (.sub a b)
    have hLeft : (run model A env a).2 ≤ (run model A env (.sub a b)).2 := by rw [run]; dsimp only; omega
    have hRight : (run model A env b).2 ≤ (run model A env (.sub a b)).2 := by rw [run]; dsimp only; omega
    have hA := ha.trans (Nat.mul_le_mul_left (2048 * a.operationBound) hLeft)
    have hB := hb.trans (Nat.mul_le_mul_left (2048 * b.operationBound) hRight)
    have h := join a.operationBound b.operationBound 0 (RationalExpression.operationBound (.sub a b))
      (run model A env (.sub a b)).2 (localFoot model A env (.sub a b))
      (live model A env a) (live model A env b) 0 hLocal hA hB (by simp)
      (by simp only [RationalExpression.operationBound]; omega)
    simpa only [live, Nat.zero_mul, Nat.max_zero] using h
  | mul a b ha hb =>
    have hLocal := GeneralPaperExpressionLocalStorage.bound model A env (.mul a b)
    have hLeft : (run model A env a).2 ≤ (run model A env (.mul a b)).2 := by rw [run]; dsimp only; omega
    have hRight : (run model A env b).2 ≤ (run model A env (.mul a b)).2 := by rw [run]; dsimp only; omega
    have hA := ha.trans (Nat.mul_le_mul_left (2048 * a.operationBound) hLeft)
    have hB := hb.trans (Nat.mul_le_mul_left (2048 * b.operationBound) hRight)
    have h := join a.operationBound b.operationBound 0 (RationalExpression.operationBound (.mul a b))
      (run model A env (.mul a b)).2 (localFoot model A env (.mul a b))
      (live model A env a) (live model A env b) 0 hLocal hA hB (by simp)
      (by simp only [RationalExpression.operationBound]; omega)
    simpa only [live, Nat.zero_mul, Nat.max_zero] using h
  | div a b ha hb =>
    have hLocal := GeneralPaperExpressionLocalStorage.bound model A env (.div a b)
    have hLeft : (run model A env a).2 ≤ (run model A env (.div a b)).2 := by rw [run]; dsimp only; omega
    have hRight : (run model A env b).2 ≤ (run model A env (.div a b)).2 := by rw [run]; dsimp only; omega
    have hA := ha.trans (Nat.mul_le_mul_left (2048 * a.operationBound) hLeft)
    have hB := hb.trans (Nat.mul_le_mul_left (2048 * b.operationBound) hRight)
    have h := join a.operationBound b.operationBound 0 (RationalExpression.operationBound (.div a b))
      (run model A env (.div a b)).2 (localFoot model A env (.div a b))
      (live model A env a) (live model A env b) 0 hLocal hA hB (by simp)
      (by simp only [RationalExpression.operationBound]; omega)
    simpa only [live, Nat.zero_mul, Nat.max_zero] using h
  | minimum a b ha hb =>
    have hLocal := GeneralPaperExpressionLocalStorage.bound model A env (.minimum a b)
    have hLeft : (run model A env a).2 ≤ (run model A env (.minimum a b)).2 := by rw [run]; dsimp only; omega
    have hRight : (run model A env b).2 ≤ (run model A env (.minimum a b)).2 := by rw [run]; dsimp only; omega
    have hA := ha.trans (Nat.mul_le_mul_left (2048 * a.operationBound) hLeft)
    have hB := hb.trans (Nat.mul_le_mul_left (2048 * b.operationBound) hRight)
    have h := join a.operationBound b.operationBound 0 (RationalExpression.operationBound (.minimum a b))
      (run model A env (.minimum a b)).2 (localFoot model A env (.minimum a b))
      (live model A env a) (live model A env b) 0 hLocal hA hB (by simp)
      (by simp only [RationalExpression.operationBound]; omega)
    simpa only [live, Nat.zero_mul, Nat.max_zero] using h
  | maximum a b ha hb =>
    have hLocal := GeneralPaperExpressionLocalStorage.bound model A env (.maximum a b)
    have hLeft : (run model A env a).2 ≤ (run model A env (.maximum a b)).2 := by rw [run]; dsimp only; omega
    have hRight : (run model A env b).2 ≤ (run model A env (.maximum a b)).2 := by rw [run]; dsimp only; omega
    have hA := ha.trans (Nat.mul_le_mul_left (2048 * a.operationBound) hLeft)
    have hB := hb.trans (Nat.mul_le_mul_left (2048 * b.operationBound) hRight)
    have h := join a.operationBound b.operationBound 0 (RationalExpression.operationBound (.maximum a b))
      (run model A env (.maximum a b)).2 (localFoot model A env (.maximum a b))
      (live model A env a) (live model A env b) 0 hLocal hA hB (by simp)
      (by simp only [RationalExpression.operationBound]; omega)
    simpa only [live, Nat.zero_mul, Nat.max_zero] using h
  | ifLe a b yes no ha hb hy hn =>
    have hLocal := GeneralPaperExpressionLocalStorage.bound model A env (.ifLe a b yes no)
    have hLeft : (run model A env a).2 ≤ (run model A env (.ifLe a b yes no)).2 := by rw [run]; dsimp only; omega
    have hRight : (run model A env b).2 ≤ (run model A env (.ifLe a b yes no)).2 := by rw [run]; dsimp only; omega
    have hA := ha.trans (Nat.mul_le_mul_left (2048 * a.operationBound) hLeft)
    have hB := hb.trans (Nat.mul_le_mul_left (2048 * b.operationBound) hRight)
    simp only [live]
    split_ifs with hc
    · have hSelected : (run model A env yes).2 ≤ (run model A env (.ifLe a b yes no)).2 := by
        rw [run]
        simp only [GeneralPaperExpressionBitExecution.compare, decide_eq_true_eq, hc, ite_true]
        omega
      have hY := hy.trans (Nat.mul_le_mul_left (2048 * yes.operationBound) hSelected)
      exact join a.operationBound b.operationBound yes.operationBound _ _ _ _ _ _ hLocal hA hB hY
        (by simp only [RationalExpression.operationBound]; have h := le_max_left yes.operationBound no.operationBound; omega)
    · have hSelected : (run model A env no).2 ≤ (run model A env (.ifLe a b yes no)).2 := by
        rw [run]
        simp only [GeneralPaperExpressionBitExecution.compare, decide_eq_true_eq, hc, ite_false]
        omega
      have hN := hn.trans (Nat.mul_le_mul_left (2048 * no.operationBound) hSelected)
      exact join a.operationBound b.operationBound no.operationBound _ _ _ _ _ _ hLocal hA hB hN
        (by simp only [RationalExpression.operationBound]; have h := le_max_right yes.operationBound no.operationBound; omega)

theorem bounded_work {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (e : RationalExpression k) (M C : ℕ) (hM : e.operationBound ≤ M) (hC : (run model A env e).2 ≤ C) :
    live model A env e ≤ 2048 * M * C :=
  (bound model A env e).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2048 hM) hC)

theorem height_bound {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (e : RationalExpression k) (s d M : ℕ) (hEnv : ∀ j, RationalHeight (env.read j) s)
    (hLit : e.LiteralHeights s) (hd : e.depth ≤ d) (hM : e.operationBound ≤ M) :
    live model A env e ≤
      2048 * M * (M * GeneralPaperExpressionBitExecution.nodeBound model A k (expressionHeightBudget s d)) :=
  bounded_work model A env e M _ hM
    (GeneralPaperExpressionBitExecution.work_height model A env e s d M hEnv hLit hd hM)

end Blotto.GeneralPaperExpressionCallLifetime
