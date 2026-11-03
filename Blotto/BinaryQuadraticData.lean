import Blotto.BinaryQuadraticExpression

/-! Data-only Boolean normalization, opcodes and selected expression evaluation
execute no work/count observers. Universal erasure proofs connect them to the
quadratic annotations; valid words/expressions exactly match the old backend.
This is an algorithm/model erasure bridge, not a verified Lean compiler or
host runtime claim. Caller array addressing and complete machine/space joins
remain separate. -/

namespace Blotto.BinaryQuadraticData
open BinaryRationalNormalization BinaryRationalOpcode

def normalize (word : SignedWord) : SignedWord :=
  let common := BinarySteinGCD.canonicalGcd word.numerator word.denominator
  let numerator := (BinaryLongDivision.divide word.numerator common).1
  let denominator := (BinaryLongDivision.divide word.denominator common).1
  ⟨word.negative && BinaryEuclideanGCD.nonzero numerator,numerator,denominator⟩

theorem normalize_erasure (word : SignedWord) :
    (BinaryQuadraticNormalization.normalizeWithWork word).1 = normalize word := by
  unfold BinaryQuadraticNormalization.normalizeWithWork normalize
  dsimp only
  rw [BinarySteinGCD.gcdWithWork_state,BinaryLongDivision.divideWithWork_refines,
    BinaryLongDivision.divideWithWork_refines]

def canonicalize (word : SignedWord) : SignedWord := trimWord (normalize word)

theorem canonicalize_erasure (word : SignedWord) :
    (BinaryQuadraticNormalization.canonicalizeWithWork word).1 = canonicalize word := by
  unfold BinaryQuadraticNormalization.canonicalizeWithWork canonicalize trimWord
  dsimp only
  rw [normalize_erasure]
  rfl

def apply (op : RealArithmeticOp) (first second : SignedWord) : SignedWord :=
  canonicalize (rawApply op first second)

theorem apply_erasure (op : RealArithmeticOp) (first second : SignedWord) :
    (BinaryQuadraticOpcode.applyWithWork op first second).1 = apply op first second :=
  canonicalize_erasure _

def expression {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → SignedWord
  | .input j => env.read j
  | .literal word => word
  | .add a b => apply .add (expression env a) (expression env b)
  | .sub a b => apply .sub (expression env a) (expression env b)
  | .mul a b => apply .mul (expression env a) (expression env b)
  | .div a b => apply .div (expression env a) (expression env b)
  | .minimum a b => apply .minimum (expression env a) (expression env b)
  | .maximum a b => apply .maximum (expression env a) (expression env b)
  | .ifLe a b yes no => if BinaryRationalArithmetic.lessEqual (expression env a) (expression env b)
      then expression env yes else expression env no

theorem expression_erasure {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) :
    (BinaryQuadraticExpression.run env e).1.1 = expression env e := by
  induction e with
  | input j => rfl
  | literal word => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [expression,BinaryQuadraticExpression.run,BinaryQuadraticExpression.combine]
      rw [ha,hb,apply_erasure]
  | ifLe a b yes no ha hb hy hn =>
      simp only [expression,BinaryQuadraticExpression.run]
      rw [ha,hb]
      split
      · exact hy
      · exact hn

theorem expression_state {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) (h : e.Valid) :
    expression env e = (e.run env).1 := by
  rw [← expression_erasure]
  exact congrArg Prod.fst (BinaryQuadraticExpression.run_state e env hEnv h)

end Blotto.BinaryQuadraticData
