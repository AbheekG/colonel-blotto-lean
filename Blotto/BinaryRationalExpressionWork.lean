import Blotto.BinaryRationalExpressionSize
import Blotto.RationalExpressionIntermediates

/-! Actual selected Boolean-expression branches have abstract bit/cell prices
from verified canonical opcodes and operand reads. Retained rational intermediate
height certificates supply widths. Compiler/address/stack/allocation pricing
remains separate; no fast-Rat or physical profiler bound is asserted. -/

namespace Blotto
open BinaryRationalNormalization BinaryRationalEncoding
namespace BinaryRationalExpression

def payloadWords (word : SignedWord) : ℕ := 1 + word.numerator.length + word.denominator.length

def opcodePrice (op : RealArithmeticOp) (x y : SignedWord) : ℕ :=
  payloadWords x + payloadWords y + (BinaryRationalOpcode.applyWithWork op x y).2 + 4

def comparePrice (x y : SignedWord) : ℕ :=
  payloadWords x + payloadWords y + BinaryRationalArithmetic.lessEqualWork x y + 4

def bitWork {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → ℕ
  | .input j => payloadWords (env.read j) + 1
  | .literal word => payloadWords word + 1
  | .add a b => a.bitWork env + b.bitWork env + opcodePrice .add (a.run env).1 (b.run env).1
  | .sub a b => a.bitWork env + b.bitWork env + opcodePrice .sub (a.run env).1 (b.run env).1
  | .mul a b => a.bitWork env + b.bitWork env + opcodePrice .mul (a.run env).1 (b.run env).1
  | .div a b => a.bitWork env + b.bitWork env + opcodePrice .div (a.run env).1 (b.run env).1
  | .minimum a b => a.bitWork env + b.bitWork env + opcodePrice .minimum (a.run env).1 (b.run env).1
  | .maximum a b => a.bitWork env + b.bitWork env + opcodePrice .maximum (a.run env).1 (b.run env).1
  | .ifLe a b yes no => a.bitWork env + b.bitWork env + comparePrice (a.run env).1 (b.run env).1 +
      if BinaryRationalArithmetic.lessEqual (a.run env).1 (b.run env).1 then yes.bitWork env else no.bitWork env

def uniformPrice (s : ℕ) : ℕ := 13000 * (2 * s + 2) ^ 3

theorem payloadWords_bound (word : SignedWord) (W : ℕ) (h : width word ≤ W) : payloadWords word ≤ 1 + 2 * W := by
  unfold payloadWords width at *
  omega

theorem opcodePrice_bound (op : RealArithmeticOp) (x y : SignedWord) (s : ℕ)
    (hX : width x ≤ 1 + 2 * s) (hY : width y ≤ 1 + 2 * s) : opcodePrice op x y ≤ uniformPrice s := by
  have hp : BinaryRationalArithmetic.pairWidth x y + 1 ≤ 2 * s + 2 := by
    unfold BinaryRationalArithmetic.pairWidth
    omega
  have hx := payloadWords_bound x _ hX
  have hy := payloadWords_bound y _ hY
  have hc := (BinaryRationalOpcode.applyWithWork_bound op x y).trans
    (Nat.mul_le_mul_left 12000 (Nat.pow_le_pow_left hp 3))
  have hLinear : 2 * s + 2 ≤ (2 * s + 2) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < 2 * s + 2 by omega) (show 1 ≤ 3 by decide)
  unfold opcodePrice uniformPrice
  omega

theorem comparePrice_bound (x y : SignedWord) (s : ℕ)
    (hX : width x ≤ 1 + 2 * s) (hY : width y ≤ 1 + 2 * s) : comparePrice x y ≤ uniformPrice s := by
  have hp : BinaryRationalArithmetic.pairWidth x y + 1 ≤ 2 * s + 2 := by
    unfold BinaryRationalArithmetic.pairWidth
    omega
  have hx := payloadWords_bound x _ hX
  have hy := payloadWords_bound y _ hY
  have hc := (BinaryRationalArithmetic.lessEqualWork_bound x y).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hp 2))
  have hSquare : (2 * s + 2) ^ 2 ≤ (2 * s + 2) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hLinear : 2 * s + 2 ≤ (2 * s + 2) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < 2 * s + 2 by omega) (show 1 ≤ 3 by decide)
  unfold comparePrice uniformPrice
  omega

theorem leafPrice_bound (word : SignedWord) (s : ℕ) (h : width word ≤ 1 + 2 * s) :
    payloadWords word + 1 ≤ uniformPrice s := by
  have he := payloadWords_bound word _ h
  have hLinear : 2 * s + 2 ≤ (2 * s + 2) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < 2 * s + 2 by omega) (show 1 ≤ 3 by decide)
  unfold uniformPrice
  omega

theorem bitWork_operations {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    e.bitWork env ≤ (e.run env).2 * uniformPrice s := by
  induction e with
  | input j =>
    have hq : RationalHeight (value (env.read j)) s := by
      simpa only [interpreted, RationalExpression.AllRunHeights, interpretedEnvironment, FixedArrayTable.read_ofFn] using hHeight
    have hW := (hEnv j).2.trans (rationalWordWidth_of_height hq)
    simp only [bitWork, run, Nat.one_mul]
    exact leafPrice_bound _ _ hW
  | literal word =>
    have hq : RationalHeight (value word) s := hHeight
    simp only [bitWork, run, Nat.one_mul]
    exact leafPrice_bound _ _ (hLit.2.trans (rationalWordWidth_of_height hq))
  | add a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .add (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    simp only [bitWork, run]
    nlinarith
  | sub a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .sub (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    simp only [bitWork, run]
    nlinarith
  | mul a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .mul (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    simp only [bitWork, run]
    nlinarith
  | div a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .div (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    simp only [bitWork, run]
    nlinarith
  | minimum a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .minimum (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    simp only [bitWork, run]
    nlinarith
  | maximum a b ha hb =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2 hHeight.2.2.2
    have hCall := opcodePrice_bound .maximum (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2 s hHeight.2.1)
    simp only [bitWork, run]
    nlinarith
  | ifLe a b yes no ha hb hy hn =>
    have hA := ha hLit.1 hHeight.2.2.1
    have hB := hb hLit.2.1 hHeight.2.2.2.1
    have hYes := hy hLit.2.2.1 hHeight.2.2.2.2.1
    have hNo := hn hLit.2.2.2 hHeight.2.2.2.2.2
    have hCompare := comparePrice_bound (a.run env).1 (b.run env).1 s
      (a.run_height_width env hEnv hLit.1 s hHeight.1)
      (b.run_height_width env hEnv hLit.2.1 s hHeight.2.1)
    simp only [bitWork, run]
    split <;> nlinarith

theorem bitWork_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    e.bitWork env ≤ e.interpreted.operationBound * uniformPrice s :=
  (e.bitWork_operations env hEnv hLit s hHeight).trans
    (Nat.mul_le_mul_right _ (e.run_count_le env (fun j => (hEnv j).1) (e.canonicalLiterals_valid hLit)))

end BinaryRationalExpression
end Blotto
