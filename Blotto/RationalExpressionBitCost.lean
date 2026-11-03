import Blotto.RationalCostModel
import Blotto.RationalExpressionIntermediates
import Blotto.RationalExpressionValue

/-! Selected-branch rational-program bit prices use actual operand widths.
A zero division still pays its equality test. Input/literal accesses pay their
word lengths. Counter, interpreter/container and physical allocator work are
separate from these primitive/copy prices. -/

namespace Blotto.RationalExpression

def pairWidth (a b : ℚ) : ℕ := max (rationalWordWidth a) (rationalWordWidth b)

def bitCost {k : ℕ} (model : RationalCostModel) (env : FixedArrayTable k ℚ) : RationalExpression k → ℕ
  | .input j => rationalWordWidth (env.read j)
  | .literal q => rationalWordWidth q
  | .add a b | .sub a b | .mul a b | .minimum a b | .maximum a b =>
    a.bitCost model env + b.bitCost model env + model.rat (pairWidth (a.run env).1 (b.run env).1)
  | .div a b =>
    a.bitCost model env + b.bitCost model env +
      model.rat (rationalWordWidth (b.run env).1) +
      if (b.run env).1 = 0 then 0 else model.rat (pairWidth (a.run env).1 (b.run env).1)
  | .ifLe a b yes no =>
    a.bitCost model env + b.bitCost model env + model.rat (pairWidth (a.run env).1 (b.run env).1) +
      if (a.run env).1 ≤ (b.run env).1 then yes.bitCost model env else no.bitCost model env

theorem pairWidth_height {a b : ℚ} {s : ℕ} (ha : RationalHeight a s) (hb : RationalHeight b s) :
    pairWidth a b ≤ 1 + 2 * s :=
  max_le (rationalWordWidth_of_height ha) (rationalWordWidth_of_height hb)

theorem bitCost_operations {k : ℕ} (model : RationalCostModel) (e : RationalExpression k)
    (env : FixedArrayTable k ℚ) (s : ℕ) (h : e.AllRunHeights env s) :
    e.bitCost model env ≤ (e.run env).2 * model.rat (1 + 2 * s) := by
  induction e with
  | input j =>
    simpa only [bitCost, run, Nat.one_mul] using (rationalWordWidth_of_height h).trans (model.word_le (1 + 2 * s))
  | literal q =>
    simpa only [bitCost, run, Nat.one_mul] using (rationalWordWidth_of_height h).trans (model.word_le (1 + 2 * s))
  | add a b ha hb | sub a b ha hb | mul a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    have ca := ha h.2.2.1
    have cb := hb h.2.2.2
    have cp := model.monotone (pairWidth_height h.1 h.2.1)
    simp only [bitCost, run]
    nlinarith
  | div a b ha hb =>
    have ca := ha h.2.2.1
    have cb := hb h.2.2.2
    have cz := model.monotone (rationalWordWidth_of_height h.2.1)
    have cp := model.monotone (pairWidth_height h.1 h.2.1)
    simp only [bitCost, run]
    split_ifs <;> nlinarith
  | ifLe a b yes no ha hb hy hn =>
    have ca := ha h.2.2.1
    have cb := hb h.2.2.2.1
    have cp := model.monotone (pairWidth_height h.1 h.2.1)
    have cy := hy h.2.2.2.2.1
    have cn := hn h.2.2.2.2.2
    simp only [bitCost, run]
    split_ifs <;> nlinarith

theorem bitCost_bound {k : ℕ} (model : RationalCostModel) (e : RationalExpression k)
    (env : FixedArrayTable k ℚ) (s : ℕ) (h : e.AllRunHeights env s) :
    e.bitCost model env ≤ e.operationBound * model.rat (1 + 2 * s) :=
  (bitCost_operations model e env s h).trans
    (Nat.mul_le_mul_right _ (e.run_operations_le env))

end Blotto.RationalExpression
