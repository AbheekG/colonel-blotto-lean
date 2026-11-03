import Blotto.BinaryExpressionCompiler
import Blotto.RationalExpressionIntermediates
import Blotto.RationalExpressionWordWidth

/-! Portable Boolean syntax has source-independent primitive work and output
height bounds from actual stored environment heights and checked finite AST
sizes. All literal words, branches and total zero divisions are covered.
No generated operand/intermediate-height oracle is supplied. -/

namespace Blotto.BinarySyntaxUniformWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler

def EnvHeight {k : ℕ} (env : FixedArrayTable k SignedWord) (s : ℕ) : Prop :=
  ∀ j, RationalHeight (value (env.read j)) s

theorem interpreted_height {k : ℕ} (env : FixedArrayTable k SignedWord) (s : ℕ) (h : EnvHeight env s) :
    ∀ j, RationalHeight ((BinaryRationalExpression.interpretedEnvironment env).read j) s := by
  intro j
  simp only [BinaryRationalExpression.interpretedEnvironment,FixedArrayTable.read_ofFn]
  exact h j

theorem constant_height (c : Constant) : RationalHeight c.rational 3 := by
  cases c <;> norm_num [Constant.rational,RationalHeight]

theorem literal_heights {k : ℕ} (e : Syntax k) (s : ℕ) (hs : 3 ≤ s) : e.rational.LiteralHeights s := by
  induction e with
  | input _ => trivial
  | literal c => exact (constant_height c).mono hs
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    exact ⟨ha,hb⟩
  | ifLe a b yes no ha hb hy hn => exact ⟨ha,hb,hy,hn⟩

theorem run_height {k : ℕ} (e : Syntax k) (env : FixedArrayTable k SignedWord)
    (hC : ∀ j, CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) :
    RationalHeight (value (e.compile.run env).1) (expressionHeightBudget s e.rational.depth) := by
  rw [e.compile_run_value env (fun j => (hC j).1)]
  exact e.rational.run_height _ s (interpreted_height env s hH) (literal_heights e s hs)

theorem run_height_bound {k : ℕ} (e : Syntax k) (env : FixedArrayTable k SignedWord)
    (hC : ∀ j, CanonicalWord (env.read j)) (s D : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s)
    (hD : e.rational.depth ≤ D) : RationalHeight (value (e.compile.run env).1) (expressionHeightBudget s D) :=
  (run_height e env hC s hs hH).mono (expressionHeightBudget_mono s hD)

theorem bitWork_bound {k : ℕ} (e : Syntax k) (env : FixedArrayTable k SignedWord)
    (hC : ∀ j, CanonicalWord (env.read j)) (s D operations : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s)
    (hD : e.rational.depth ≤ D) (hOperations : e.rational.operationBound ≤ operations) :
    e.compile.bitWork env ≤ operations * BinaryRationalExpression.uniformPrice (expressionHeightBudget s D) := by
  have hAll := e.rational.run_all_heights (BinaryRationalExpression.interpretedEnvironment env) s (interpreted_height env s hH) (literal_heights e s hs)
  have hBudget := RationalExpression.AllRunHeights_mono e.rational _ (expressionHeightBudget_mono s hD) hAll
  have hWork := e.compile.bitWork_bound env hC e.compile_canonical (expressionHeightBudget s D) (by
    rw [e.compile_interpreted]; exact hBudget)
  rw [e.compile_interpreted] at hWork
  exact hWork.trans (Nat.mul_le_mul_right _ hOperations)

end Blotto.BinarySyntaxUniformWork
