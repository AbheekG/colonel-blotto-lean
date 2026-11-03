import Blotto.RationalExpressionValue

/-! Real evaluation of the retained counted local expression language.
Safe total division and selected-only conditionals keep the same operation
allowance. The real-RAM primitive model is separate from physical allocation. -/

namespace Blotto.RationalExpression
open scoped Classical

noncomputable def runReal {k : ℕ} (env : FixedArrayTable k ℝ) : RationalExpression k → ℝ × ℕ
  | .input j => (env.read j, 1)
  | .literal q => (q, 1)
  | .add a b => let x := a.runReal env; let y := b.runReal env; (x.1 + y.1, x.2 + y.2 + 1)
  | .sub a b => let x := a.runReal env; let y := b.runReal env; (x.1 - y.1, x.2 + y.2 + 1)
  | .mul a b => let x := a.runReal env; let y := b.runReal env; (x.1 * y.1, x.2 + y.2 + 1)
  | .div a b => let x := a.runReal env; let y := b.runReal env; (if y.1 = 0 then 0 else x.1 / y.1, x.2 + y.2 + 2)
  | .minimum a b => let x := a.runReal env; let y := b.runReal env; (min x.1 y.1, x.2 + y.2 + 1)
  | .maximum a b => let x := a.runReal env; let y := b.runReal env; (max x.1 y.1, x.2 + y.2 + 1)
  | .ifLe a b yes no =>
    let x := a.runReal env
    let y := b.runReal env
    let z := if x.1 ≤ y.1 then yes.runReal env else no.runReal env
    (z.1, x.2 + y.2 + z.2 + 1)

noncomputable def realValue {k : ℕ} (e : RationalExpression k) (env : FixedArrayTable k ℝ) : ℝ := (e.runReal env).1

theorem runReal_operations_le {k : ℕ} (e : RationalExpression k) (env : FixedArrayTable k ℝ) :
    (e.runReal env).2 ≤ e.operationBound := by
  induction e with
  | input j => rfl
  | literal q => rfl
  | add a b ha hb => simp only [runReal, operationBound]; omega
  | sub a b ha hb => simp only [runReal, operationBound]; omega
  | mul a b ha hb => simp only [runReal, operationBound]; omega
  | div a b ha hb => simp only [runReal, operationBound]; omega
  | minimum a b ha hb => simp only [runReal, operationBound]; omega
  | maximum a b ha hb => simp only [runReal, operationBound]; omega
  | ifLe a b yes no ha hb hy hn =>
    simp only [runReal, operationBound]
    split
    · have hmax := le_max_left yes.operationBound no.operationBound
      omega
    · have hmax := le_max_right yes.operationBound no.operationBound
      omega

@[simp] theorem realValue_input {k : ℕ} (j : Fin k) (env : FixedArrayTable k ℝ) :
    (.input j : RationalExpression k).realValue env = env.read j := rfl
@[simp] theorem realValue_literal {k : ℕ} (q : ℚ) (env : FixedArrayTable k ℝ) :
    (.literal q : RationalExpression k).realValue env = q := rfl
@[simp] theorem realValue_add {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℝ) :
    (add a b).realValue env = a.realValue env + b.realValue env := rfl
@[simp] theorem realValue_sub {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℝ) :
    (sub a b).realValue env = a.realValue env - b.realValue env := rfl
@[simp] theorem realValue_mul {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℝ) :
    (mul a b).realValue env = a.realValue env * b.realValue env := rfl
@[simp] theorem realValue_div {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℝ) :
    (div a b).realValue env = a.realValue env / b.realValue env := by
  simp only [realValue, runReal]
  split
  · simp_all
  · rfl
@[simp] theorem realValue_minimum {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℝ) :
    (minimum a b).realValue env = min (a.realValue env) (b.realValue env) := rfl
@[simp] theorem realValue_maximum {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℝ) :
    (maximum a b).realValue env = max (a.realValue env) (b.realValue env) := rfl
@[simp] theorem realValue_ifLe {k : ℕ} (a b yes no : RationalExpression k) (env : FixedArrayTable k ℝ) :
    (ifLe a b yes no).realValue env = if a.realValue env ≤ b.realValue env then yes.realValue env else no.realValue env := by
  simp only [realValue, runReal]
  split
  · rename_i h
    exact (ite_eq_left h).symm
  · rename_i h
    exact (ite_eq_right h).symm

@[simp] theorem realValue_power {k : ℕ} (e : RationalExpression k) (n : ℕ) (env : FixedArrayTable k ℝ) :
    (e.power n).realValue env = e.realValue env ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ]

end Blotto.RationalExpression
