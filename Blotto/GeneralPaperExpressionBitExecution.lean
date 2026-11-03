import Blotto.GeneralPaperEqualRoutedPreparation

/-! Fused rational-expression execution at the declared paper bit prices.
Each child and selected continuation executes once. Actual rational inputs,
results, comparisons, references and interpreter control are charged. -/
namespace Blotto.GeneralPaperExpressionBitExecution
open GeneralPaperRationalScalarStep (Op)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def unit (A count : ℕ) : ℕ := 64 * (A + binaryWordWidth (count + 1) + 1)

def compare (model : RationalCostModel) (A : ℕ) (a b : ℚ) : Bool × ℕ :=
  (decide (a ≤ b), rationalWordWidth a + rationalWordWidth b +
    model.rat (max (rationalWordWidth a) (rationalWordWidth b)) + 32 * A + 32)

def run {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ) : RationalExpression k → ℚ × ℕ
  | .input j => (env.read j, rationalWordWidth (env.read j) + unit A env.data.size)
  | .literal q => (q, rationalWordWidth q + unit A env.data.size)
  | .add a b =>
      let x := run model A env a
      let y := run model A env b
      let z := GeneralPaperRationalScalarStep.run model A .add x.1 y.1
      (z.1, x.2 + y.2 + z.2 + unit A env.data.size)
  | .sub a b =>
      let x := run model A env a
      let y := run model A env b
      let z := GeneralPaperRationalScalarStep.run model A .sub x.1 y.1
      (z.1, x.2 + y.2 + z.2 + unit A env.data.size)
  | .mul a b =>
      let x := run model A env a
      let y := run model A env b
      let z := GeneralPaperRationalScalarStep.run model A .mul x.1 y.1
      (z.1, x.2 + y.2 + z.2 + unit A env.data.size)
  | .div a b =>
      let x := run model A env a
      let y := run model A env b
      let z := GeneralPaperRationalScalarStep.run model A .div x.1 y.1
      (z.1, x.2 + y.2 + z.2 + unit A env.data.size)
  | .minimum a b =>
      let x := run model A env a
      let y := run model A env b
      let c := compare model A x.1 y.1
      let z := if c.1 then x.1 else y.1
      (z, x.2 + y.2 + c.2 + rationalWordWidth z + unit A env.data.size)
  | .maximum a b =>
      let x := run model A env a
      let y := run model A env b
      let c := compare model A x.1 y.1
      let z := if c.1 then y.1 else x.1
      (z, x.2 + y.2 + c.2 + rationalWordWidth z + unit A env.data.size)
  | .ifLe a b yes no =>
      let x := run model A env a
      let y := run model A env b
      let c := compare model A x.1 y.1
      let z := if c.1 then run model A env yes else run model A env no
      (z.1, x.2 + y.2 + c.2 + z.2 + unit A env.data.size)

theorem data {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ) (e : RationalExpression k) :
    (run model A env e).1 = (e.run env).1 := by
  induction e with
  | input j => rfl
  | literal q => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [run, GeneralPaperRationalScalarStep.run, Op.apply, RationalExpression.run, ha, hb]
  | div a b ha hb =>
    simp only [run, GeneralPaperRationalScalarStep.run, Op.apply, ha, hb]
    exact (RationalExpression.safe_div_value a b env).symm
  | minimum a b ha hb =>
    simp only [run, compare, RationalExpression.run, ha, hb, decide_eq_true_eq]
    split_ifs with h <;> simp [min_def, h]
  | maximum a b ha hb =>
    simp only [run, compare, RationalExpression.run, ha, hb, decide_eq_true_eq]
    split_ifs with h <;> simp [max_def, h]
  | ifLe a b yes no ha hb hy hn =>
    simp only [run, compare, RationalExpression.run, ha, hb, decide_eq_true_eq]
    split_ifs <;> assumption

def nodeBound (model : RationalCostModel) (A k s : ℕ) : ℕ :=
  8 * model.rat (1 + 2 * s) + 2 * unit A k

theorem leaf_bound (model : RationalCostModel) (A k s : ℕ) (q : ℚ) (hq : RationalHeight q s) :
    rationalWordWidth q + unit A k ≤ nodeBound model A k s := by
  have h := (rationalWordWidth_of_height hq).trans (model.word_le _)
  unfold nodeBound
  omega

theorem scalar_bound (model : RationalCostModel) (A k s : ℕ) (op : Op) (a b : ℚ)
    (ha : RationalHeight a s) (hb : RationalHeight b s) (ho : RationalHeight (op.apply a b) s) :
    (GeneralPaperRationalScalarStep.run model A op a b).2 + unit A k ≤ nodeBound model A k s := by
  have h := GeneralPaperRationalScalarStep.work model A op a b s ha hb ho
  unfold nodeBound unit
  omega

theorem compare_copy_bound (model : RationalCostModel) (A k s : ℕ) (a b z : ℚ)
    (ha : RationalHeight a s) (hb : RationalHeight b s) (hz : RationalHeight z s) :
    (compare model A a b).2 + rationalWordWidth z + unit A k ≤ nodeBound model A k s := by
  have h1 := (rationalWordWidth_of_height ha).trans (model.word_le _)
  have h2 := (rationalWordWidth_of_height hb).trans (model.word_le _)
  have h3 := (rationalWordWidth_of_height hz).trans (model.word_le _)
  have h4 := model.monotone (max_le (rationalWordWidth_of_height ha) (rationalWordWidth_of_height hb))
  unfold compare nodeBound unit
  dsimp only
  omega

theorem compare_bound (model : RationalCostModel) (A k s : ℕ) (a b : ℚ)
    (ha : RationalHeight a s) (hb : RationalHeight b s) :
    (compare model A a b).2 + unit A k ≤ nodeBound model A k s := by
  have h := compare_copy_bound model A k s a b a ha hb ha
  omega

theorem work {k s : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ) (e : RationalExpression k)
    (h : e.AllRunHeights env s) (ho : RationalHeight (e.run env).1 s) :
    (run model A env e).2 ≤ e.operationBound * nodeBound model A k s := by
  induction e with
  | input j =>
    simpa only [run, env.size, RationalExpression.operationBound, Nat.one_mul] using leaf_bound model A k s (env.read j) h
  | literal q =>
    simpa only [run, env.size, RationalExpression.operationBound, Nat.one_mul] using leaf_bound model A k s q h
  | add a b ha hb =>
    have ca := ha h.2.2.1 h.1
    have cb := hb h.2.2.2 h.2.1
    have cs := scalar_bound model A k s .add (a.run env).1 (b.run env).1 h.1 h.2.1 ho
    simp only [run, data, env.size, RationalExpression.operationBound]
    nlinarith only [ca, cb, cs]
  | sub a b ha hb =>
    have ca := ha h.2.2.1 h.1
    have cb := hb h.2.2.2 h.2.1
    have cs := scalar_bound model A k s .sub (a.run env).1 (b.run env).1 h.1 h.2.1 ho
    simp only [run, data, env.size, RationalExpression.operationBound]
    nlinarith only [ca, cb, cs]
  | mul a b ha hb =>
    have ca := ha h.2.2.1 h.1
    have cb := hb h.2.2.2 h.2.1
    have cs := scalar_bound model A k s .mul (a.run env).1 (b.run env).1 h.1 h.2.1 ho
    simp only [run, data, env.size, RationalExpression.operationBound]
    nlinarith only [ca, cb, cs]
  | div a b ha hb =>
    have ca := ha h.2.2.1 h.1
    have cb := hb h.2.2.2 h.2.1
    have hValue : (RationalExpression.run env (.div a b)).1 = (a.run env).1 / (b.run env).1 :=
      RationalExpression.safe_div_value a b env
    rw [hValue] at ho
    have cs := scalar_bound model A k s .div (a.run env).1 (b.run env).1 h.1 h.2.1 ho
    simp only [run, data, env.size, RationalExpression.operationBound]
    nlinarith only [ca, cb, cs]
  | minimum a b ha hb =>
    have ca := ha h.2.2.1 h.1
    have cb := hb h.2.2.2 h.2.1
    have cs := compare_copy_bound model A k s (a.run env).1 (b.run env).1 (min (a.run env).1 (b.run env).1) h.1 h.2.1 ho
    simp only [run, data, compare, env.size, RationalExpression.operationBound, decide_eq_true_eq]
    unfold compare at cs
    dsimp only at cs
    split_ifs with hc <;> simp only [min_def, hc, ite_true, ite_false] at cs <;> nlinarith only [ca, cb, cs]
  | maximum a b ha hb =>
    have ca := ha h.2.2.1 h.1
    have cb := hb h.2.2.2 h.2.1
    have cs := compare_copy_bound model A k s (a.run env).1 (b.run env).1 (max (a.run env).1 (b.run env).1) h.1 h.2.1 ho
    simp only [run, data, compare, env.size, RationalExpression.operationBound, decide_eq_true_eq]
    unfold compare at cs
    dsimp only at cs
    split_ifs with hc
    · rw [max_eq_right hc] at cs
      nlinarith only [ca, cb, cs]
    · rw [max_eq_left (le_of_not_ge hc)] at cs
      nlinarith only [ca, cb, cs]
  | ifLe a b yes no ha hb hy hn =>
    have ca := ha h.2.2.1 h.1
    have cb := hb h.2.2.2.1 h.2.1
    have cs := compare_bound model A k s (a.run env).1 (b.run env).1 h.1 h.2.1
    simp only [RationalExpression.run] at ho
    simp only [run, data, env.size, RationalExpression.operationBound, compare, decide_eq_true_eq]
    unfold compare at cs
    dsimp only at cs
    split_ifs with hc
    · rw [ite_eq_left hc] at ho
      have cy := hy h.2.2.2.2.1 ho
      have hm := Nat.mul_le_mul_right (nodeBound model A k s) (le_max_left yes.operationBound no.operationBound)
      nlinarith only [ca, cb, cs, cy, hm]
    · rw [ite_eq_right hc] at ho
      have cn := hn h.2.2.2.2.2 ho
      have hm := Nat.mul_le_mul_right (nodeBound model A k s) (le_max_right yes.operationBound no.operationBound)
      nlinarith only [ca, cb, cs, cn, hm]

theorem work_height {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ)
    (e : RationalExpression k) (s d M : ℕ) (hEnv : ∀ j, RationalHeight (env.read j) s)
    (hLit : e.LiteralHeights s) (hd : e.depth ≤ d) (hM : e.operationBound ≤ M) :
    (run model A env e).2 ≤ M * nodeBound model A k (expressionHeightBudget s d) := by
  have hm := expressionHeightBudget_mono s hd
  have hAll := RationalExpression.AllRunHeights_mono e env hm (e.run_all_heights env s hEnv hLit)
  have hOut := (e.run_height env s hEnv hLit).mono hm
  exact (work model A env e hAll hOut).trans (Nat.mul_le_mul_right _ hM)

end Blotto.GeneralPaperExpressionBitExecution
