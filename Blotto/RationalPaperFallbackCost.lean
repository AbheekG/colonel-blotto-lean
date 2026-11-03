import Blotto.RationalLottoPaperProgram
import Blotto.RationalCostModel

/-! The paper's direct exhaustion row prices rational read/write words only.
It performs no coupling-tree traversal or rational arithmetic. Fin comparison,
row allocation and physical ownership remain separate. No coordinate-box
claim is added to the existing hard-budget fallback guarantee. -/

namespace Blotto.RationalLottoResourceSystem
open scoped BigOperators

def fallbackRowBitCost {n : ℕ} (i : RationalLottoResourceSystem n) : ℕ :=
  2 * ∑ j : Fin n, rationalWordWidth (i.fallbackAllocation j)

theorem fallbackRowBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (s : ℕ) (hs : 2 ≤ s) (hB : RationalHeight i.B s) :
    i.fallbackRowBitCost ≤ 2 * n * model.rat (1 + 2 * s) := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hFields : ∀ j, RationalHeight (i.fallbackAllocation j) s := by
    intro j
    unfold fallbackAllocation
    split <;> assumption
  have hp : (∑ j : Fin n, rationalWordWidth (i.fallbackAllocation j)) ≤ n * model.rat (1 + 2 * s) := by
    calc
      _ ≤ ∑ _j : Fin n, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (hFields j)).trans (model.word_le _))
      _ = _ := by simp
  unfold fallbackRowBitCost
  nlinarith

def paperFallbackBitWork {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  match (i.runShared K R outerBits scalarBits choiceBits).1 with
  | none => i.fallbackRowBitCost
  | some _ => 0

theorem paperFallbackBitWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (s : ℕ) (hs : 2 ≤ s) (hB : RationalHeight i.B s) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.paperFallbackBitWork K R outerBits scalarBits choiceBits ≤ 2 * n * model.rat (1 + 2 * s) := by
  unfold paperFallbackBitWork
  split
  · exact i.fallbackRowBitCost_bound model s hs hB
  · exact Nat.zero_le _

theorem paperFallbackBitWork_of_none {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool)
    (hNone : (i.runShared K R outerBits scalarBits choiceBits).1 = none) :
    i.paperFallbackBitWork K R outerBits scalarBits choiceBits = i.fallbackRowBitCost := by
  simp only [paperFallbackBitWork, hNone]

theorem paperFallbackBitWork_of_some {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) (x : Fin n → ℚ)
    (hSome : (i.runShared K R outerBits scalarBits choiceBits).1 = some x) :
    i.paperFallbackBitWork K R outerBits scalarBits choiceBits = 0 := by
  simp only [paperFallbackBitWork, hSome]

end Blotto.RationalLottoResourceSystem
