import Blotto.GeneralPaperEqualRealPreparationRates

/-! Named exact-real arithmetic executes each counted segment expression
with the same value. Selected branches and zero division agree; its primitive
trace is bounded by the actual executed operation count, not a size oracle. -/
namespace Blotto.GeneralPaperRealSegmentPrimitives
open PRGRealRAMExecution
set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable def environment {k : ℕ} (env : FixedArrayTable k ℚ) : FixedArrayTable k ℝ :=
  FixedArrayTable.ofFn (fun j => (env.read j : ℝ))

theorem value {k : ℕ} (env : FixedArrayTable k ℚ) (e : RationalExpression k) :
    e.realValue (environment env) = ((e.run env).1 : ℝ) := by
  induction e with
  | input j => simp only [RationalExpression.realValue_input, environment, FixedArrayTable.read_ofFn, RationalExpression.run]
  | literal q => rfl
  | add a b ha hb => simp only [RationalExpression.realValue_add, RationalExpression.run, ha, hb, Rat.cast_add]
  | sub a b ha hb => simp only [RationalExpression.realValue_sub, RationalExpression.run, ha, hb, Rat.cast_sub]
  | mul a b ha hb => simp only [RationalExpression.realValue_mul, RationalExpression.run, ha, hb, Rat.cast_mul]
  | div a b ha hb => rw [RationalExpression.realValue_div, RationalExpression.safe_div_value, Rat.cast_div, ha, hb]
  | minimum a b ha hb =>
    simp only [RationalExpression.realValue_minimum, RationalExpression.run, ha, hb]
    norm_cast
  | maximum a b ha hb =>
    simp only [RationalExpression.realValue_maximum, RationalExpression.run, ha, hb]
    norm_cast
  | ifLe a b yes no ha hb hy hn =>
    have ho : ((a.run env).1 : ℝ) ≤ ((b.run env).1 : ℝ) ↔ (a.run env).1 ≤ (b.run env).1 := by norm_cast
    simp only [RationalExpression.realValue_ifLe, RationalExpression.run, ha, hb, ho]
    split_ifs <;> assumption

theorem primitive_value {k : ℕ} (env : FixedArrayTable k ℚ) (e : RationalExpression k) :
    (expression (environment env) e).value = ((e.run env).1 : ℝ) := by
  rw [expression_value, value]

theorem primitive_cost {k : ℕ} (env : FixedArrayTable k ℚ) (e : RationalExpression k) :
    (expression (environment env) e).cost ≤ 2 * (e.run env).2 := by
  induction e with
  | input j | literal q => simp [expression, loadReal, Run.cost, Operation.cost, RationalExpression.run]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    simp only [expression, RationalExpression.run]
    apply (binary_cost _ _ _).trans
    omega
  | ifLe a b yes no ha hb hy hn =>
    have ho : ((a.run env).1 : ℝ) ≤ ((b.run env).1 : ℝ) ↔ (a.run env).1 ≤ (b.run env).1 := by norm_cast
    simp only [expression, expression_value, value, compareLe, decide_eq_true_eq, ho, RationalExpression.run]
    split
    · unfold Run.cost at *
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Operation.cost]
      omega
    · unfold Run.cost at *
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Operation.cost]
      omega

theorem callback_price {k : ℕ} (env : FixedArrayTable k ℚ) (e : RationalExpression k) :
    (expression (environment env) e).cost + 32 ≤ 8 * (e.run env).2 + 32 := by
  have h := primitive_cost env e
  omega

end Blotto.GeneralPaperRealSegmentPrimitives
