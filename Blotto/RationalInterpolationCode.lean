import Blotto.RationalExpressionLiteralHeight
import Blotto.RationalExpressionIntermediates
import Blotto.RationalSegmentLottery

/-! Counted rational segment interpolation used by every local descriptor.
The certificate separates endpoint/parameter heights from random-bit decoding. -/

namespace Blotto.RationalInterpolationCode

abbrev Expr := RationalExpression 3

def program : Expr := .add (.mul (.sub (.literal 1) (.input 2)) (.input 0)) (.mul (.input 2) (.input 1))

def environment (P Q t : ℚ) : FixedArrayTable 3 ℚ := FixedArrayTable.ofFn ![P, Q, t]

theorem value_eq (P Q t : ℚ) : program.value (environment P Q t) = (1 - t) * P + t * Q := by
  simp [program, environment, FixedArrayTable.read_ofFn]

theorem operations : program.operationBound = 9 := by decide

theorem depth : program.depth = 3 := by decide

theorem literals : program.LiteralHeights 2 := by norm_num [program, RationalExpression.LiteralHeights, RationalHeight]

theorem output_height (P Q t : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hP : RationalHeight P s) (hQ : RationalHeight Q s) (ht : RationalHeight t s) :
    RationalHeight ((1 - t) * P + t * Q) (expressionHeightBudget s 3) := by
  have hEnv : ∀ j, RationalHeight ((environment P Q t).read j) s := by
    intro j
    fin_cases j
    · simpa [environment, FixedArrayTable.read_ofFn] using hP
    · simpa [environment, FixedArrayTable.read_ofFn] using hQ
    · simpa [environment, FixedArrayTable.read_ofFn] using ht
  have h := program.run_height _ s hEnv (program.LiteralHeights_mono hs literals)
  change RationalHeight (program.value (environment P Q t)) (expressionHeightBudget s program.depth) at h
  rw [value_eq, depth] at h
  exact h

theorem output_wordWidth (P Q t : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hP : RationalHeight P s) (hQ : RationalHeight Q s) (ht : RationalHeight t s) :
    rationalWordWidth ((1 - t) * P + t * Q) ≤ 1 + 2 * expressionHeightBudget s 3 :=
  rationalWordWidth_of_height (output_height P Q t s hs hP hQ ht)

end Blotto.RationalInterpolationCode
