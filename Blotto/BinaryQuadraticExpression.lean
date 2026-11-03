import Blotto.BinaryQuadraticOpcode
import Blotto.BinaryRationalExpressionWork

/-! Actual selected Boolean expression evaluation uses the quadratic opcodes,
retaining exactly the old output word, operation count and conditional choice.
Canonical stored source inputs/literals and rational trace heights derive
quadratic work per reached node. The annotation is erasable; array-address,
control-record and whole-caller execution/storage remain separate. -/

namespace Blotto.BinaryQuadraticExpression
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalExpression

def opcodePrice (op : RealArithmeticOp) (x y : SignedWord) : ℕ :=
  payloadWords x + payloadWords y + (BinaryQuadraticOpcode.applyWithWork op x y).2 + 4

def combine (op : RealArithmeticOp) (control : ℕ) (x y : (SignedWord × ℕ) × ℕ) : (SignedWord × ℕ) × ℕ :=
  let result := BinaryQuadraticOpcode.applyWithWork op x.1.1 y.1.1
  ((result.1,x.1.2+y.1.2+control),x.2+y.2+payloadWords x.1.1+payloadWords y.1.1+result.2+4)

def run {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → (SignedWord × ℕ) × ℕ
  | .input j => ((env.read j,1),payloadWords (env.read j)+1)
  | .literal word => ((word,1),payloadWords word+1)
  | .add a b => combine .add 1 (run env a) (run env b)
  | .sub a b => combine .sub 1 (run env a) (run env b)
  | .mul a b => combine .mul 1 (run env a) (run env b)
  | .div a b => combine .div 2 (run env a) (run env b)
  | .minimum a b => combine .minimum 1 (run env a) (run env b)
  | .maximum a b => combine .maximum 1 (run env a) (run env b)
  | .ifLe a b yes no =>
      let x := run env a
      let y := run env b
      let next := if BinaryRationalArithmetic.lessEqual x.1.1 y.1.1 then run env yes else run env no
      ((next.1.1,x.1.2+y.1.2+next.1.2+1),x.2+y.2+comparePrice x.1.1 y.1.1+next.2)

theorem run_state {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) (h : e.Valid) :
    (run env e).1 = e.run env := by
  induction e with
  | input j => rfl
  | literal word => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    have hA := a.run_valid env hEnv h.1
    have hB := b.run_valid env hEnv h.2
    simp only [run,combine,BinaryRationalExpression.run]
    rw [ha h.1,hb h.2,BinaryQuadraticOpcode.applyWithWork_state _ _ _ hA hB]
  | ifLe a b yes no ha hb hy hn =>
    simp only [run,BinaryRationalExpression.run]
    rw [ha h.1,hb h.2.1]
    split
    · rw [hy h.2.2.1]
    · rw [hn h.2.2.2]

def uniformPrice (s : ℕ) : ℕ := 12000 * (2*s+2)^2

theorem opcodePrice_bound (op : RealArithmeticOp) (x y : SignedWord) (s : ℕ)
    (hx : width x ≤ 1+2*s) (hy : width y ≤ 1+2*s) : opcodePrice op x y ≤ uniformPrice s := by
  have hw : BinaryRationalArithmetic.pairWidth x y+1 ≤ 2*s+2 := by unfold BinaryRationalArithmetic.pairWidth; omega
  have hcx := payloadWords_bound x _ hx
  have hcy := payloadWords_bound y _ hy
  have h := (BinaryQuadraticOpcode.applyWithWork_bound op x y).trans
    (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left hw 2))
  unfold opcodePrice uniformPrice
  nlinarith

theorem comparePrice_bound (x y : SignedWord) (s : ℕ)
    (hx : width x ≤ 1+2*s) (hy : width y ≤ 1+2*s) : comparePrice x y ≤ uniformPrice s := by
  have hw : BinaryRationalArithmetic.pairWidth x y+1 ≤ 2*s+2 := by unfold BinaryRationalArithmetic.pairWidth; omega
  have hcx := payloadWords_bound x _ hx
  have hcy := payloadWords_bound y _ hy
  have h := (BinaryRationalArithmetic.lessEqualWork_bound x y).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hw 2))
  unfold comparePrice uniformPrice
  nlinarith

theorem leafPrice_bound (word : SignedWord) (s : ℕ) (h : width word ≤ 1+2*s) :
    payloadWords word+1 ≤ uniformPrice s := by
  have hp := payloadWords_bound word _ h
  unfold uniformPrice
  nlinarith

theorem run_work_operations {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    (run env e).2 ≤ (e.run env).2 * uniformPrice s := by
  induction e with
  | input j =>
    have hq : RationalHeight (value (env.read j)) s := by
      simpa only [interpreted, RationalExpression.AllRunHeights, interpretedEnvironment, FixedArrayTable.read_ofFn] using hHeight
    have hW := (hEnv j).2.trans (rationalWordWidth_of_height hq)
    simp only [run, BinaryRationalExpression.run, Nat.one_mul]
    exact leafPrice_bound _ _ hW
  | literal word =>
    have hq : RationalHeight (value word) s := hHeight
    simp only [run, BinaryRationalExpression.run, Nat.one_mul]
    exact leafPrice_bound _ _ (hLit.2.trans (rationalWordWidth_of_height hq))
  | add a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .add (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    have hSA := run_state a env (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)
    have hSB := run_state b env (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)
    simp only [run,combine,BinaryRationalExpression.run]
    rw [hSA,hSB]
    unfold opcodePrice at hCall
    nlinarith
  | sub a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .sub (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    have hSA := run_state a env (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)
    have hSB := run_state b env (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)
    simp only [run,combine,BinaryRationalExpression.run]
    rw [hSA,hSB]
    unfold opcodePrice at hCall
    nlinarith
  | mul a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .mul (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    have hSA := run_state a env (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)
    have hSB := run_state b env (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)
    simp only [run,combine,BinaryRationalExpression.run]
    rw [hSA,hSB]
    unfold opcodePrice at hCall
    nlinarith
  | div a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .div (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    have hSA := run_state a env (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)
    have hSB := run_state b env (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)
    simp only [run,combine,BinaryRationalExpression.run]
    rw [hSA,hSB]
    unfold opcodePrice at hCall
    nlinarith
  | minimum a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .minimum (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    have hSA := run_state a env (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)
    have hSB := run_state b env (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)
    simp only [run,combine,BinaryRationalExpression.run]
    rw [hSA,hSB]
    unfold opcodePrice at hCall
    nlinarith
  | maximum a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .maximum (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    have hSA := run_state a env (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)
    have hSB := run_state b env (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)
    simp only [run,combine,BinaryRationalExpression.run]
    rw [hSA,hSB]
    unfold opcodePrice at hCall
    nlinarith
  | ifLe a b yes no ha hb hy hn =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2.1 hHeight.2.2.2.1
    have hYes := hy hLit.2.2.1 hHeight.2.2.2.2.1
    have hNo := hn hLit.2.2.2 hHeight.2.2.2.2.2
    have hCompare := comparePrice_bound (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2.1 s hHeight.2.1)
    have hSA := run_state a env (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)
    have hSB := run_state b env (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2.1)
    simp only [run,BinaryRationalExpression.run]
    rw [hSA,hSB]
    split <;> nlinarith

theorem run_work_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    (run env e).2 ≤ e.interpreted.operationBound * uniformPrice s :=
  (run_work_operations e env hEnv hLit s hHeight).trans
    (Nat.mul_le_mul_right _ (e.run_count_le env (fun j => (hEnv j).1) (e.canonicalLiterals_valid hLit)))

end Blotto.BinaryQuadraticExpression
