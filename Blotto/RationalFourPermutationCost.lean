import Blotto.RationalPermutationPreparation

/-! Four-coordinate output permutations retain the dense matrix products.
Every partial row has at most one nonzero term, so rational intermediate words
keep the input height. Input production and index/backend work are separate. -/

namespace Blotto.RationalFourPermutationCode
open scoped BigOperators

abbrev Expr := RationalExpression 4
def row (k : Fin 4) : Expr :=
  .add (.add (.add (.add (.add (.literal 0)
    (.mul (.literal (if k = 0 then 1 else 0)) (.input 0)))
      (.mul (.literal (if k = 1 then 1 else 0)) (.input 1)))
        (.mul (.literal (if k = 2 then 1 else 0)) (.input 2)))
          (.mul (.literal (if k = 3 then 1 else 0)) (.input 3))) (.literal 0)
def environment (x : Fin 4 → ℚ) : FixedArrayTable 4 ℚ := FixedArrayTable.ofFn x

theorem row_value (k : Fin 4) (x : Fin 4 → ℚ) : (row k).value (environment x) = x k := by
  fin_cases k <;> simp [row, environment, FixedArrayTable.read_ofFn]

theorem row_operations (k : Fin 4) : (row k).operationBound ≤ 19 := by fin_cases k <;> decide

theorem row_intermediates (k : Fin 4) (x : Fin 4 → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hX : ∀ j, RationalHeight (x j) s) : (row k).AllRunHeights (environment x) s := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  fin_cases k <;> simp [row, environment, FixedArrayTable.read_ofFn,
    RationalExpression.AllRunHeights, RationalExpression.run, hX, hZero, hOne]

theorem row_permutation_value (π : Equiv.Perm (Fin 4)) (x : Fin 4 → ℚ) (j : Fin 4) :
    (row (π j)).value (environment x) = (RationalAffineAllocation.permutation π).value x j := by
  rw [row_value, RationalAffineAllocation.permutation_value]

def rowBitCost (model : RationalCostModel) (π : Equiv.Perm (Fin 4)) (x : Fin 4 → ℚ) (j : Fin 4) : ℕ :=
  (row (π j)).bitCost model (environment x) + rationalWordWidth ((RationalAffineAllocation.permutation π).value x j)

theorem rowBitCost_bound (model : RationalCostModel) (π : Equiv.Perm (Fin 4)) (x : Fin 4 → ℚ)
    (j : Fin 4) (s : ℕ) (hs : 2 ≤ s) (hX : ∀ k, RationalHeight (x k) s) :
    rowBitCost model π x j ≤ 20 * model.rat (1 + 2 * s) := by
  have hc := ((row (π j)).bitCost_bound model _ _ (row_intermediates (π j) x s hs hX)).trans
    (Nat.mul_le_mul_right _ (row_operations (π j)))
  have hw := (rationalWordWidth_of_height (hX (π j))).trans (model.word_le _)
  unfold rowBitCost
  rw [RationalAffineAllocation.permutation_value]
  omega

def outputBitCost (model : RationalCostModel) (π : Equiv.Perm (Fin 4)) (x : Fin 4 → ℚ) : ℕ :=
  ∑ j : Fin 4, rowBitCost model π x j

theorem outputBitCost_bound (model : RationalCostModel) (π : Equiv.Perm (Fin 4)) (x : Fin 4 → ℚ)
    (s : ℕ) (hs : 2 ≤ s) (hX : ∀ k, RationalHeight (x k) s) :
    outputBitCost model π x ≤ 80 * model.rat (1 + 2 * s) := by
  calc
    _ ≤ ∑ _j : Fin 4, 20 * model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ => rowBitCost_bound model π x j s hs hX)
    _ = _ := by simp; ring

end Blotto.RationalFourPermutationCode
