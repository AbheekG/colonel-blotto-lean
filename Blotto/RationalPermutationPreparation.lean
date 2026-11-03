import Blotto.RationalTerminalHeight
import Blotto.RationalExpressionBitCost
import Blotto.PreparedSegmentDescriptorHeight

/-! The dense three-coordinate affine permutation retains all nine products.
Each row has at most one nonzero coefficient, so every rational intermediate
has the supplied coordinate height. Index/tag work is separate. -/

namespace Blotto.RationalPermutationCode
open scoped BigOperators

abbrev Expr := RationalExpression 3

def row (k : Fin 3) : Expr :=
  .add (.add (.add (.add (.literal 0)
    (.mul (.literal (if k = 0 then 1 else 0)) (.input 0)))
      (.mul (.literal (if k = 1 then 1 else 0)) (.input 1)))
        (.mul (.literal (if k = 2 then 1 else 0)) (.input 2))) (.literal 0)

def environment (x : Fin 3 → ℚ) : FixedArrayTable 3 ℚ := FixedArrayTable.ofFn x

theorem row_value (k : Fin 3) (x : Fin 3 → ℚ) : (row k).value (environment x) = x k := by
  fin_cases k <;> simp [row, environment, FixedArrayTable.read_ofFn]

theorem row_operations (k : Fin 3) : (row k).operationBound ≤ 15 := by fin_cases k <;> decide

theorem row_intermediates (k : Fin 3) (x : Fin 3 → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hX : ∀ j, RationalHeight (x j) s) : (row k).AllRunHeights (environment x) s := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  fin_cases k <;> simp [row, environment, FixedArrayTable.read_ofFn,
    RationalExpression.AllRunHeights, RationalExpression.run, hX, hZero, hOne]

theorem row_bitCost (model : RationalCostModel) (k : Fin 3) (x : Fin 3 → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hX : ∀ j, RationalHeight (x j) s) :
    (row k).bitCost model (environment x) ≤ 15 * model.rat (1 + 2 * s) :=
  ((row k).bitCost_bound model _ _ (row_intermediates k x s hs hX)).trans
    (Nat.mul_le_mul_right _ (row_operations k))

theorem row_permutation_value (π : Equiv.Perm (Fin 3)) (x : Fin 3 → ℚ) (j : Fin 3) :
    (row (π j)).value (environment x) = (RationalAffineAllocation.permutation π).value x j := by
  rw [row_value, RationalAffineAllocation.permutation_value]

def descriptorFormulaBitCost (model : RationalCostModel) (l : RationalSegmentLottery 3 18)
    (π : Equiv.Perm (Fin 3)) : ℕ :=
  (∑ slot : Fin 18, ∑ j : Fin 3, (row (π j)).bitCost model (environment (l.P slot))) +
    ∑ slot : Fin 18, ∑ j : Fin 3, (row (π j)).bitCost model (environment (l.Q slot))

theorem descriptorFormulaBitCost_bound (model : RationalCostModel) (l : RationalSegmentLottery 3 18)
    (π : Equiv.Perm (Fin 3)) (s : ℕ) (hs : 2 ≤ s) (h : l.HeightAt s) :
    descriptorFormulaBitCost model l π ≤ 1620 * model.rat (1 + 2 * s) := by
  have hP : (∑ slot : Fin 18, ∑ j : Fin 3, (row (π j)).bitCost model (environment (l.P slot))) ≤
      18 * (3 * (15 * model.rat (1 + 2 * s))) := by
    calc
      _ ≤ ∑ _slot : Fin 18, ∑ _j : Fin 3, 15 * model.rat (1 + 2 * s) := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => row_bitCost model _ _ s hs (fun r => (h.2 slot r).1)))
      _ = _ := by simp
  have hQ : (∑ slot : Fin 18, ∑ j : Fin 3, (row (π j)).bitCost model (environment (l.Q slot))) ≤
      18 * (3 * (15 * model.rat (1 + 2 * s))) := by
    calc
      _ ≤ ∑ _slot : Fin 18, ∑ _j : Fin 3, 15 * model.rat (1 + 2 * s) := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => row_bitCost model _ _ s hs (fun r => (h.2 slot r).2)))
      _ = _ := by simp
  unfold descriptorFormulaBitCost
  nlinarith

def preparedDescriptorBitCost (model : RationalCostModel) (l : RationalSegmentLottery 3 18)
    (π : Equiv.Perm (Fin 3)) : ℕ :=
  descriptorFormulaBitCost model l π + (PreparedSegmentDescriptor.prepare (l.mapped (RationalAffineAllocation.permutation π))).payloadBitCost

theorem preparedDescriptorBitCost_bound (model : RationalCostModel) (l : RationalSegmentLottery 3 18)
    (π : Equiv.Perm (Fin 3)) (s : ℕ) (hs : 2 ≤ s) (h : l.HeightAt s) :
    preparedDescriptorBitCost model l π ≤ 1746 * model.rat (1 + 2 * s) := by
  have hf := descriptorFormulaBitCost_bound model l π s hs h
  have hp := (PreparedSegmentDescriptor.prepare (l.mapped (RationalAffineAllocation.permutation π))).payloadBitCost_bound s
    (h.mapped_permutation π)
  have hc := hp.trans (Nat.mul_le_mul_left 126 (model.word_le _))
  unfold preparedDescriptorBitCost
  omega

end Blotto.RationalPermutationCode
