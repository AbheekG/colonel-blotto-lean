import Blotto.PreparedSegmentDescriptor
import Blotto.RationalLotteryHeight

/-! Stored descriptor payload is bounded by all weight/endpoint word heights.
This is logical data size, separate from physical allocation or ownership. -/

namespace Blotto.PreparedSegmentDescriptor
open scoped BigOperators

theorem payloadBitCost_bound {n k : ℕ} {l : RationalSegmentLottery n k} (p : PreparedSegmentDescriptor l)
    (s : ℕ) (h : l.HeightAt s) : p.payloadBitCost ≤ (k + 2 * k * n) * (1 + 2 * s) := by
  have hw : (∑ slot, rationalWordWidth (p.weights.read slot)) ≤ k * (1 + 2 * s) := by
    calc
      _ ≤ ∑ _slot : Fin k, (1 + 2 * s) := Finset.sum_le_sum (fun slot _ => by
        rw [p.weight_correct]; exact rationalWordWidth_of_height (h.1 slot))
      _ = _ := by simp
  have hp : (∑ slot, ∑ j, rationalWordWidth ((p.left.read slot).read j)) ≤ k * n * (1 + 2 * s) := by
    calc
      _ ≤ ∑ _slot : Fin k, ∑ _j : Fin n, (1 + 2 * s) := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => by rw [p.left_correct]; exact rationalWordWidth_of_height (h.2 slot j).1))
      _ = _ := by simp; ring
  have hq : (∑ slot, ∑ j, rationalWordWidth ((p.right.read slot).read j)) ≤ k * n * (1 + 2 * s) := by
    calc
      _ ≤ ∑ _slot : Fin k, ∑ _j : Fin n, (1 + 2 * s) := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => by rw [p.right_correct]; exact rationalWordWidth_of_height (h.2 slot j).2))
      _ = _ := by simp; ring
  unfold payloadBitCost
  nlinarith

end Blotto.PreparedSegmentDescriptor
