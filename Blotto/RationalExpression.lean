import Blotto.RationalHeightAdd
import Blotto.FixedArrayTable

/-! A counted local rational arithmetic program. Safe division tests zero
explicitly, and conditionals evaluate only their selected continuation.
Native coupling-formula compilation into these programs remains separate. -/

namespace Blotto

inductive RationalExpression (k : ℕ) where
  | input (j : Fin k)
  | literal (q : ℚ)
  | add (a b : RationalExpression k)
  | sub (a b : RationalExpression k)
  | mul (a b : RationalExpression k)
  | div (a b : RationalExpression k)
  | minimum (a b : RationalExpression k)
  | maximum (a b : RationalExpression k)
  | ifLe (a b yes no : RationalExpression k)

namespace RationalExpression

def run {k : ℕ} (env : FixedArrayTable k ℚ) : RationalExpression k → ℚ × ℕ
  | .input j => (env.read j, 1)
  | .literal q => (q, 1)
  | .add a b => let x := a.run env; let y := b.run env; (x.1 + y.1, x.2 + y.2 + 1)
  | .sub a b => let x := a.run env; let y := b.run env; (x.1 - y.1, x.2 + y.2 + 1)
  | .mul a b => let x := a.run env; let y := b.run env; (x.1 * y.1, x.2 + y.2 + 1)
  | .div a b => let x := a.run env; let y := b.run env; (if y.1 = 0 then 0 else x.1 / y.1, x.2 + y.2 + 2)
  | .minimum a b => let x := a.run env; let y := b.run env; (min x.1 y.1, x.2 + y.2 + 1)
  | .maximum a b => let x := a.run env; let y := b.run env; (max x.1 y.1, x.2 + y.2 + 1)
  | .ifLe a b yes no =>
    let x := a.run env
    let y := b.run env
    let z := if x.1 ≤ y.1 then yes.run env else no.run env
    (z.1, x.2 + y.2 + z.2 + 1)

def operationBound {k : ℕ} : RationalExpression k → ℕ
  | .input _ | .literal _ => 1
  | .add a b | .sub a b | .mul a b | .minimum a b | .maximum a b => a.operationBound + b.operationBound + 1
  | .div a b => a.operationBound + b.operationBound + 2
  | .ifLe a b yes no => a.operationBound + b.operationBound + max yes.operationBound no.operationBound + 1

def depth {k : ℕ} : RationalExpression k → ℕ
  | .input _ | .literal _ => 0
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => max a.depth b.depth + 1
  | .ifLe a b yes no => max (max a.depth b.depth) (max yes.depth no.depth) + 1

def LiteralHeights {k : ℕ} (s : ℕ) : RationalExpression k → Prop
  | .input _ => True
  | .literal q => RationalHeight q s
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => a.LiteralHeights s ∧ b.LiteralHeights s
  | .ifLe a b yes no => a.LiteralHeights s ∧ b.LiteralHeights s ∧ yes.LiteralHeights s ∧ no.LiteralHeights s

theorem run_operations_le {k : ℕ} (e : RationalExpression k) (env : FixedArrayTable k ℚ) :
    (e.run env).2 ≤ e.operationBound := by
  induction e with
  | input j => rfl
  | literal q => rfl
  | add a b ha hb => simp only [run, operationBound]; omega
  | sub a b ha hb => simp only [run, operationBound]; omega
  | mul a b ha hb => simp only [run, operationBound]; omega
  | div a b ha hb => simp only [run, operationBound]; omega
  | minimum a b ha hb => simp only [run, operationBound]; omega
  | maximum a b ha hb => simp only [run, operationBound]; omega
  | ifLe a b yes no ha hb hy hn =>
    simp only [run, operationBound]
    split
    · have hmax := le_max_left yes.operationBound no.operationBound
      omega
    · have hmax := le_max_right yes.operationBound no.operationBound
      omega

theorem safe_div_value {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℚ) :
    ((.div a b : RationalExpression k).run env).1 = (a.run env).1 / (b.run env).1 := by
  simp only [run]
  split
  · simp_all
  · rfl

end RationalExpression
end Blotto
