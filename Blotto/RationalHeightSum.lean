import Blotto.RationalHeightAdd

/-! Finite rational sums have bit height linear in list length and operand
height. Cancellation and zero sums need no special domain restriction. -/

namespace Blotto.RationalHeight

theorem list_sum {l : List ℚ} {s : ℕ} (h : ∀ q ∈ l, RationalHeight q s) :
    RationalHeight l.sum ((s + 1) * l.length + 1) := by
  induction l with
  | nil => norm_num [RationalHeight]
  | cons q rest ih =>
    have hq := h q (by simp)
    have hrest := ih (fun r hr => h r (by simp [hr]))
    have hsum := hq.add hrest
    have hm : s + ((s + 1) * rest.length + 1) + 1 ≤ (s + 1) * (q :: rest).length + 1 := by
      simp only [List.length_cons, Nat.mul_succ]
      omega
    simpa only [List.sum_cons] using hsum.mono hm

theorem abs {q : ℚ} {s : ℕ} (h : RationalHeight q s) : RationalHeight |q| s := by
  by_cases hq : 0 ≤ q
  · rw [abs_of_nonneg hq]; exact h
  · rw [abs_of_neg (lt_of_not_ge hq)]; exact h.neg

end Blotto.RationalHeight
