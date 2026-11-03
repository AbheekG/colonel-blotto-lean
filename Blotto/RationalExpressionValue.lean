import Blotto.RationalExpressionWordWidth

/-! Value equations used to refine maintained native arithmetic formulas
into counted programs. Safe division agrees with rational total division. -/

namespace Blotto.RationalExpression

def value {k : ℕ} (e : RationalExpression k) (env : FixedArrayTable k ℚ) : ℚ := (e.run env).1

@[simp] theorem value_input {k : ℕ} (j : Fin k) (env : FixedArrayTable k ℚ) :
    (.input j : RationalExpression k).value env = env.read j := rfl

@[simp] theorem value_literal {k : ℕ} (q : ℚ) (env : FixedArrayTable k ℚ) :
    (.literal q : RationalExpression k).value env = q := rfl

@[simp] theorem value_add {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℚ) :
    (add a b).value env = a.value env + b.value env := rfl

@[simp] theorem value_sub {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℚ) :
    (sub a b).value env = a.value env - b.value env := rfl

@[simp] theorem value_mul {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℚ) :
    (mul a b).value env = a.value env * b.value env := rfl

@[simp] theorem value_div {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℚ) :
    (div a b).value env = a.value env / b.value env := safe_div_value a b env

@[simp] theorem value_minimum {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℚ) :
    (minimum a b).value env = min (a.value env) (b.value env) := rfl

@[simp] theorem value_maximum {k : ℕ} (a b : RationalExpression k) (env : FixedArrayTable k ℚ) :
    (maximum a b).value env = max (a.value env) (b.value env) := rfl

@[simp] theorem value_ifLe {k : ℕ} (a b yes no : RationalExpression k) (env : FixedArrayTable k ℚ) :
    (ifLe a b yes no).value env = if a.value env ≤ b.value env then yes.value env else no.value env := by
  simp only [value, run]
  split
  · rename_i h
    exact (ite_eq_left h).symm
  · rename_i h
    exact (ite_eq_right h).symm

def power {k : ℕ} (e : RationalExpression k) : ℕ → RationalExpression k
  | 0 => .literal 1
  | n + 1 => .mul (e.power n) e

@[simp] theorem value_power {k : ℕ} (e : RationalExpression k) (n : ℕ) (env : FixedArrayTable k ℚ) :
    (e.power n).value env = e.value env ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ]

end Blotto.RationalExpression
