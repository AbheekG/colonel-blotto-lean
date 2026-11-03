import Blotto.RationalHeightSum
import Blotto.RationalThreeInputHeight

/-! Primitive height propagation at a common fixed expression level. -/

namespace Blotto.RationalHeight

theorem add_level {q r : ℚ} {s d : ℕ} (hq : RationalHeight q (expressionHeightBudget s d))
    (hr : RationalHeight r (expressionHeightBudget s d)) :
    RationalHeight (q + r) (expressionHeightBudget s (d + 1)) := by
  simpa only [expressionHeightBudget_succ, two_mul] using hq.add hr

theorem sub_level {q r : ℚ} {s d : ℕ} (hq : RationalHeight q (expressionHeightBudget s d))
    (hr : RationalHeight r (expressionHeightBudget s d)) :
    RationalHeight (q - r) (expressionHeightBudget s (d + 1)) := by
  simpa only [expressionHeightBudget_succ, two_mul] using hq.sub hr

theorem mul_level {q r : ℚ} {s d : ℕ} (hq : RationalHeight q (expressionHeightBudget s d))
    (hr : RationalHeight r (expressionHeightBudget s d)) :
    RationalHeight (q * r) (expressionHeightBudget s (d + 1)) := by
  exact (hq.mul hr).mono (by rw [expressionHeightBudget_succ]; omega)

theorem div_level {q r : ℚ} {s d : ℕ} (hq : RationalHeight q (expressionHeightBudget s d))
    (hr : RationalHeight r (expressionHeightBudget s d)) :
    RationalHeight (q / r) (expressionHeightBudget s (d + 1)) := by
  exact (hq.div hr).mono (by rw [expressionHeightBudget_succ]; omega)

end Blotto.RationalHeight
