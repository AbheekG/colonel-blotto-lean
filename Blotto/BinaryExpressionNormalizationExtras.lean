import Blotto.BinaryQuadraticSyntaxMeasured
import Blotto.BinaryNormalizationExtraWork

/-! Bounds for the normalization field returned by the selected structural
expression and syntax producers. Only reached branches contribute. Their old
result/trace/source records and all original price hypotheses remain exact.
This source-price join does not price new counter/record/native evaluations. -/
namespace Blotto.BinaryExpressionNormalizationExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryQuadraticExpressionMeasured
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem combine_bound (op : RealArithmeticOp) (a b : ((SignedWord × Trace) × ℕ) × ℕ)
    (ha : a.2 ≤ 155*a.1.2) (hb : b.2 ≤ 155*b.1.2) :
    (combineWithExtras op a b).2 ≤ 155*(combineWithExtras op a b).1.2 := by
  have h := BinaryNormalizationExtraWork.opcode_bound op a.1.1.1 b.1.1.1
  simp only [combineWithExtras]
  omega

theorem evaluate_bound {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    (evaluateWithExtras env e).2 ≤ 155*(evaluateWithExtras env e).1.2 := by
  induction e with
  | input _ | literal _ => simp only [evaluateWithExtras]; omega
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      exact combine_bound _ _ _ ha hb
  | ifLe a b yes no ha hb hy hn =>
      simp only [evaluateWithExtras]
      split <;> omega

theorem evaluate_selected {k : ℕ} (env : FixedArrayTable k SignedWord)
    (a b yes no : BinaryRationalExpression k) :
    (evaluateWithExtras env (.ifLe a b yes no)).2 =
      (evaluateWithExtras env a).2+(evaluateWithExtras env b).2+
        (if (compare (evaluateWithExtras env a).1.1.1 (evaluateWithExtras env b).1.1.1).1.1
          then (evaluateWithExtras env yes).2 else (evaluateWithExtras env no).2) := by
  simp only [evaluateWithExtras]
  split <;> rfl

theorem evaluate_price {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (BinaryRationalExpression.interpretedEnvironment env) s) :
    (evaluateWithExtras env e).1.2+(evaluateWithExtras env e).2 ≤
      156*(e.interpreted.operationBound*BinaryQuadraticExpression.uniformPrice s) := by
  have he := evaluate_bound env e
  have hw := evaluate_work_bound env e hEnv hLit s hHeight
  rw [← evaluateWithExtras_compat] at hw
  omega

theorem syntax_bound {k : ℕ} (env : FixedArrayTable k SignedWord) (source : BinaryExpressionCompiler.Syntax k) :
    (BinaryQuadraticSyntaxMeasured.runWithExtras env source).2 ≤
      155*(BinaryQuadraticSyntaxMeasured.runWithExtras env source).1.2 := by
  have he := evaluate_bound env (BinaryQuadraticSyntaxMeasured.compileWithTrace source).1.1
  simp only [BinaryQuadraticSyntaxMeasured.runWithExtras]
  omega

theorem syntax_price {k : ℕ} (env : FixedArrayTable k SignedWord) (source : BinaryExpressionCompiler.Syntax k)
    (hC : ∀ j,CanonicalWord (env.read j)) (s D operations nodes : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) (hD : source.rational.depth ≤ D)
    (hOperations : source.rational.operationBound ≤ operations) (hNodes : source.nodes ≤ nodes) :
    (BinaryQuadraticSyntaxMeasured.runWithExtras env source).1.2+
      (BinaryQuadraticSyntaxMeasured.runWithExtras env source).2 ≤
      156*BinaryQuadraticSyntaxMeasured.workEnvelope nodes operations s D := by
  have he := syntax_bound env source
  have hw := BinaryQuadraticSyntaxMeasured.run_work env source hC s D operations nodes hs hH hD hOperations hNodes
  rw [← BinaryQuadraticSyntaxMeasured.runWithExtras_compat] at hw
  omega

end Blotto.BinaryExpressionNormalizationExtras
