import Blotto.RationalInterpolationCode
import Blotto.RationalExpressionBitCost
import Blotto.RationalHeightBudget

/-! Interpolation prices the actual expression, available endpoint/parameter
materialization and result word. Scalar bit decoding, descriptor reads, address
work, list/array allocation and the physical backend remain separate. -/

namespace Blotto.RationalInterpolationCode

def bitCost (model : RationalCostModel) (P Q t : ℚ) : ℕ :=
  program.bitCost model (environment P Q t)

theorem bitCost_bound (model : RationalCostModel) (P Q t : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hP : RationalHeight P s) (hQ : RationalHeight Q s) (ht : RationalHeight t s) :
    bitCost model P Q t ≤ 9 * model.rat (1 + 2 * expressionHeightBudget s 3) := by
  have hEnv : ∀ j, RationalHeight ((environment P Q t).read j) s := by
    intro j
    fin_cases j
    · simpa [environment, FixedArrayTable.read_ofFn] using hP
    · simpa [environment, FixedArrayTable.read_ofFn] using hQ
    · simpa [environment, FixedArrayTable.read_ofFn] using ht
  have hAll := program.run_all_heights _ s hEnv (program.LiteralHeights_mono hs literals)
  rw [depth] at hAll
  have h := program.bitCost_bound model _ _ hAll
  simpa only [bitCost, operations] using h

def materializedBitCost (model : RationalCostModel) (P Q t : ℚ) : ℕ :=
  rationalWordWidth P + rationalWordWidth Q + rationalWordWidth t + bitCost model P Q t +
    rationalWordWidth ((1 - t) * P + t * Q)

theorem materializedBitCost_bound (model : RationalCostModel) (P Q t : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hP : RationalHeight P s) (hQ : RationalHeight Q s) (ht : RationalHeight t s) :
    materializedBitCost model P Q t ≤ 13 * model.rat (1 + 2 * expressionHeightBudget s 3) := by
  let W := 1 + 2 * expressionHeightBudget s 3
  have hm := expressionHeightBudget_ge_input s 3
  have hp := (rationalWordWidth_of_height (hP.mono hm)).trans (model.word_le W)
  have hq := (rationalWordWidth_of_height (hQ.mono hm)).trans (model.word_le W)
  have ht' := (rationalWordWidth_of_height (ht.mono hm)).trans (model.word_le W)
  have ho := (output_wordWidth P Q t s hs hP hQ ht).trans (model.word_le W)
  have hc := bitCost_bound model P Q t s hs hP hQ ht
  change bitCost model P Q t ≤ 9 * model.rat W at hc
  change materializedBitCost model P Q t ≤ 13 * model.rat W
  unfold materializedBitCost
  omega

theorem arithmetic_primitives (P Q t : ℚ) : (program.run (environment P Q t)).2 ≤ 9 := by
  simpa only [operations] using program.run_operations_le (environment P Q t)

end Blotto.RationalInterpolationCode
