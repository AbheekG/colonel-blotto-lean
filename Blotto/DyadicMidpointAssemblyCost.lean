import Blotto.DyadicMidpointHeight
import Blotto.RationalExpressionBitCost
import Blotto.RationalExpressionLiteralHeight
import Blotto.RationalHeightBudget

/-! The native midpoint numerator and final fraction agree with a counted
rational expression. Index decoding and the denominator's natural shift are
separate. Prices cover available scalar words and rational primitives only. -/

namespace Blotto.DyadicMidpointAssembly

abbrev Expr := RationalExpression 2

def program : Expr := .div (.add (.mul (.input 0) (.literal 2)) (.literal 1)) (.input 1)

def environment (K : ℕ) (bits : Fin K → Bool) : FixedArrayTable 2 ℚ :=
  FixedArrayTable.ofFn ![((balancedBitIndex K bits).val : ℚ), ((1 <<< (K + 1) : ℕ) : ℚ)]

theorem value_eq (K : ℕ) (bits : Fin K → Bool) :
    program.value (environment K bits) = dyadicMidpointSample K bits := by
  simp [program, environment, FixedArrayTable.read_ofFn, dyadicMidpointSample]

theorem operations : program.operationBound = 8 := by decide

theorem depth : program.depth = 3 := by decide

theorem literals : program.LiteralHeights 2 := by
  norm_num [program, RationalExpression.LiteralHeights, RationalHeight]

theorem nat_height (n s : ℕ) (hs : 0 < s) (hn : n < 2 ^ s) : RationalHeight (n : ℚ) s := by
  have h := RationalHeight.fraction (n : ℤ) 1 s (by decide) (by simpa using hn)
    (by exact Nat.one_lt_two_pow hs.ne')
  simpa using h

theorem environment_height (K : ℕ) (bits : Fin K → Bool) :
    ∀ j, RationalHeight ((environment K bits).read j) (K + 2) := by
  have hIndex := (balancedBitIndex K bits).isLt.trans_le
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show K ≤ K + 2 by omega))
  have hDen : (1 <<< (K + 1) : ℕ) < 2 ^ (K + 2) := by
    rw [Nat.shiftLeft_eq, one_mul, show K + 2 = (K + 1) + 1 by omega, pow_succ]
    have hp := Nat.two_pow_pos (K + 1)
    omega
  intro j
  fin_cases j
  · simpa [environment, FixedArrayTable.read_ofFn] using nat_height _ (K + 2) (by omega) hIndex
  · simpa [environment, FixedArrayTable.read_ofFn] using nat_height _ (K + 2) (by omega) hDen

def bitCost (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  program.bitCost model (environment K bits)

theorem bitCost_bound (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) :
    bitCost model K bits ≤ 8 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) := by
  have hAll := program.run_all_heights _ (K + 2) (environment_height K bits)
    (program.LiteralHeights_mono (by omega) literals)
  rw [depth] at hAll
  have h := program.bitCost_bound model _ _ hAll
  simpa only [bitCost, operations] using h

def materializedBitCost (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  rationalWordWidth ((environment K bits).read 0) + rationalWordWidth ((environment K bits).read 1) +
    bitCost model K bits + rationalWordWidth (dyadicMidpointSample K bits)

theorem materializedBitCost_bound (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) :
    materializedBitCost model K bits ≤ 11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) := by
  let W := 1 + 2 * expressionHeightBudget (K + 2) 3
  have hm := expressionHeightBudget_ge_input (K + 2) 3
  have hi := (rationalWordWidth_of_height ((environment_height K bits 0).mono hm)).trans (model.word_le W)
  have hd := (rationalWordWidth_of_height ((environment_height K bits 1).mono hm)).trans (model.word_le W)
  have ho := (rationalWordWidth_of_height ((dyadicMidpointSample_height K bits).mono hm)).trans (model.word_le W)
  have hc := bitCost_bound model K bits
  change bitCost model K bits ≤ 8 * model.rat W at hc
  change materializedBitCost model K bits ≤ 11 * model.rat W
  unfold materializedBitCost
  omega

end Blotto.DyadicMidpointAssembly
