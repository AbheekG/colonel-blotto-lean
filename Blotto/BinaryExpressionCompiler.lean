import Blotto.BinaryRationalExpressionStorage

/-! Native expression compilation from a portable finite constant alphabet.
Literal words are explicit Boolean data (0,1,2,4); the compiler traverses the
syntax and never converts a Rat value or enumerates represented Nat bits.
Arbitrary rational input preparation remains separate; environments already
contain stored canonical signed words. Rational syntax is a specification. -/

namespace Blotto.BinaryExpressionCompiler
open BinaryRationalNormalization BinaryRationalEncoding

inductive Constant where
  | zero | one | two | four
  deriving DecidableEq, Repr

def Constant.word : Constant → SignedWord
  | .zero => ⟨false, [], [true]⟩
  | .one => ⟨false, [true], [true]⟩
  | .two => ⟨false, [false, true], [true]⟩
  | .four => ⟨false, [false, false, true], [true]⟩

def Constant.rational : Constant → ℚ
  | .zero => 0 | .one => 1 | .two => 2 | .four => 4

theorem Constant.word_value (c : Constant) : value c.word = c.rational := by
  cases c <;> norm_num [Constant.word, Constant.rational, value, BinaryBigEndian.littleValue]

theorem Constant.word_canonical (c : Constant) : CanonicalWord c.word := by
  constructor
  · cases c <;> change 0 < (1 : ℕ) <;> decide
  · rw [Constant.word_value]
    cases c <;> decide

theorem Constant.word_payload (c : Constant) :
    BinaryRationalExpression.payloadWords c.word ≤ 5 := by cases c <;> decide

inductive Syntax (k : ℕ) where
  | input (j : Fin k)
  | literal (c : Constant)
  | add (a b : Syntax k)
  | sub (a b : Syntax k)
  | mul (a b : Syntax k)
  | div (a b : Syntax k)
  | minimum (a b : Syntax k)
  | maximum (a b : Syntax k)
  | ifLe (a b yes no : Syntax k)

namespace Syntax

def compile {k : ℕ} : Syntax k → BinaryRationalExpression k
  | .input j => .input j
  | .literal c => .literal c.word
  | .add a b => .add a.compile b.compile
  | .sub a b => .sub a.compile b.compile
  | .mul a b => .mul a.compile b.compile
  | .div a b => .div a.compile b.compile
  | .minimum a b => .minimum a.compile b.compile
  | .maximum a b => .maximum a.compile b.compile
  | .ifLe a b yes no => .ifLe a.compile b.compile yes.compile no.compile

def rational {k : ℕ} : Syntax k → RationalExpression k
  | .input j => .input j
  | .literal c => .literal c.rational
  | .add a b => .add a.rational b.rational
  | .sub a b => .sub a.rational b.rational
  | .mul a b => .mul a.rational b.rational
  | .div a b => .div a.rational b.rational
  | .minimum a b => .minimum a.rational b.rational
  | .maximum a b => .maximum a.rational b.rational
  | .ifLe a b yes no => .ifLe a.rational b.rational yes.rational no.rational

theorem compile_interpreted {k : ℕ} (e : Syntax k) : e.compile.interpreted = e.rational := by
  induction e <;> simp only [compile, rational, BinaryRationalExpression.interpreted,
    Constant.word_value, *]

theorem compile_canonical {k : ℕ} (e : Syntax k) : e.compile.CanonicalLiterals := by
  induction e with
  | input _ => trivial
  | literal c => exact c.word_canonical
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      exact ⟨ha, hb⟩
  | ifLe a b yes no ha hb hy hn => exact ⟨ha, hb, hy, hn⟩

def nodes {k : ℕ} : Syntax k → ℕ
  | .input _ | .literal _ => 1
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => 1 + a.nodes + b.nodes
  | .ifLe a b yes no => 1 + a.nodes + b.nodes + yes.nodes + no.nodes

-- Every emitted syntax node is charged once, and its explicitly stored literal
-- payload is charged separately; sharing can only reduce this allowance.
def compileAllocated {k : ℕ} : Syntax k → ℕ
  | .input _ => 1
  | .literal c => 1 + c.word.numerator.length + c.word.denominator.length + 1
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => 1 + a.compileAllocated + b.compileAllocated
  | .ifLe a b yes no => 1 + a.compileAllocated + b.compileAllocated + yes.compileAllocated + no.compileAllocated

def compileWithAllocation {k : ℕ} (e : Syntax k) : BinaryRationalExpression k × ℕ :=
  (e.compile, e.compileAllocated)

theorem compileAllocated_bound {k : ℕ} (e : Syntax k) : e.compileAllocated ≤ 6 * e.nodes := by
  induction e with
  | input _ => simp [compileAllocated, nodes]
  | literal c => cases c <;> simp [compileAllocated, nodes, Constant.word]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [compileAllocated, nodes]; omega
  | ifLe a b yes no ha hb hy hn => simp only [compileAllocated, nodes]; omega

theorem compile_literalPayload {k : ℕ} (e : Syntax k) : e.compile.literalPayload ≤ 5 * e.compile.literalCount := by
  induction e with
  | input _ => simp [compile, BinaryRationalExpression.literalPayload, BinaryRationalExpression.literalCount]
  | literal c => exact c.word_payload
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [compile, BinaryRationalExpression.literalPayload, BinaryRationalExpression.literalCount]; omega
  | ifLe a b yes no ha hb hy hn =>
      simp only [compile, BinaryRationalExpression.literalPayload, BinaryRationalExpression.literalCount]; omega

theorem compile_run_value {k : ℕ} (e : Syntax k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) :
    value (e.compile.run env).1 = (e.rational.run (BinaryRationalExpression.interpretedEnvironment env)).1 := by
  have h := e.compile.run_value env hEnv (e.compile.canonicalLiterals_valid e.compile_canonical)
  rw [e.compile_interpreted] at h
  exact h

theorem compile_run_count {k : ℕ} (e : Syntax k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) :
    (e.compile.run env).2 = (e.rational.run (BinaryRationalExpression.interpretedEnvironment env)).2 := by
  have h := e.compile.run_count env hEnv (e.compile.canonicalLiterals_valid e.compile_canonical)
  rw [e.compile_interpreted] at h
  exact h

end Syntax
end Blotto.BinaryExpressionCompiler
