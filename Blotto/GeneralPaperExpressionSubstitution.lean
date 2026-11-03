import Blotto.GeneralPaperExpressionBitExecution

/-! Static substitution compiles the fixed segment formulas to expressions
over their original five-word input. It depends on no numerical input data.
The semantic and syntax bounds are separate from runtime execution prices. -/
namespace Blotto.GeneralPaperExpressionSubstitution
set_option autoImplicit false
set_option maxHeartbeats 1400000

def bind {k r : ℕ} (inputs : Fin k → RationalExpression r) : RationalExpression k → RationalExpression r
  | .input j => inputs j
  | .literal q => .literal q
  | .add a b => .add (bind inputs a) (bind inputs b)
  | .sub a b => .sub (bind inputs a) (bind inputs b)
  | .mul a b => .mul (bind inputs a) (bind inputs b)
  | .div a b => .div (bind inputs a) (bind inputs b)
  | .minimum a b => .minimum (bind inputs a) (bind inputs b)
  | .maximum a b => .maximum (bind inputs a) (bind inputs b)
  | .ifLe a b yes no => .ifLe (bind inputs a) (bind inputs b) (bind inputs yes) (bind inputs no)

theorem data {k r : ℕ} (inputs : Fin k → RationalExpression r) (env : FixedArrayTable r ℚ)
    (e : RationalExpression k) :
    ((bind inputs e).run env).1 = (e.run (FixedArrayTable.ofFn (fun j => ((inputs j).run env).1))).1 := by
  induction e with
  | input j => simp only [bind, RationalExpression.run, FixedArrayTable.read_ofFn]
  | literal q => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    simp only [bind, RationalExpression.run, ha, hb]
  | ifLe a b yes no ha hb hy hn =>
    simp only [bind, RationalExpression.run, ha, hb]
    split_ifs <;> assumption

theorem depth {k r : ℕ} (inputs : Fin k → RationalExpression r) (D : ℕ)
    (h : ∀ j, (inputs j).depth ≤ D) (e : RationalExpression k) : (bind inputs e).depth ≤ e.depth + D := by
  induction e with
  | input j => simpa only [bind, RationalExpression.depth, Nat.zero_add] using h j
  | literal q => simp [bind, RationalExpression.depth]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    simp only [bind, RationalExpression.depth]
    omega
  | ifLe a b yes no ha hb hy hn =>
    simp only [bind, RationalExpression.depth]
    omega

theorem operations {k r : ℕ} (inputs : Fin k → RationalExpression r) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ j, (inputs j).operationBound ≤ M) (e : RationalExpression k) :
    (bind inputs e).operationBound ≤ e.operationBound * M := by
  induction e with
  | input j => simpa only [bind, RationalExpression.operationBound, Nat.one_mul] using h j
  | literal q => simpa only [bind, RationalExpression.operationBound, Nat.one_mul] using hM
  | add a b ha hb | sub a b ha hb | mul a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    simp only [bind, RationalExpression.operationBound]
    nlinarith only [ha, hb, hM]
  | div a b ha hb =>
    simp only [bind, RationalExpression.operationBound]
    nlinarith only [ha, hb, hM]
  | ifLe a b yes no ha hb hy hn =>
    have hm := max_le (hy.trans (Nat.mul_le_mul_right M (le_max_left yes.operationBound no.operationBound)))
      (hn.trans (Nat.mul_le_mul_right M (le_max_right yes.operationBound no.operationBound)))
    simp only [bind, RationalExpression.operationBound]
    nlinarith only [ha, hb, hm, hM]

theorem literals {k r s : ℕ} (inputs : Fin k → RationalExpression r)
    (h : ∀ j, (inputs j).LiteralHeights s) (e : RationalExpression k) (he : e.LiteralHeights s) :
    (bind inputs e).LiteralHeights s := by
  induction e with
  | input j => exact h j
  | literal q => exact he
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    exact ⟨ha he.1, hb he.2⟩
  | ifLe a b yes no ha hb hy hn => exact ⟨ha he.1, hb he.2.1, hy he.2.2.1, hn he.2.2.2⟩

end Blotto.GeneralPaperExpressionSubstitution
