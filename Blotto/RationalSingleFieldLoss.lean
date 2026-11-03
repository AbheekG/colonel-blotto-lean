import Blotto.ProductGibbsTraining

/-! Executable rational half-tie losses, including a zero tie, refine canonical
real shares. Only one selected field contributes to each action's update. -/

namespace Blotto
namespace SparseMW

def rationalShare (bid opponent : ℚ) : ℚ :=
  if opponent < bid then 1 else if bid = opponent then 1 / 2 else 0

theorem rationalShare_real (bid opponent : ℚ) :
    (rationalShare bid opponent : ℝ) = share (bid : ℝ) (opponent : ℝ) := by
  unfold rationalShare share
  have hlt : (opponent : ℝ) < (bid : ℝ) ↔ opponent < bid := by norm_cast
  have heq : (bid : ℝ) = (opponent : ℝ) ↔ bid = opponent := by norm_cast
  simp only [hlt, heq]
  split_ifs <;> norm_num

theorem rationalShare_unit (bid opponent : ℚ) :
    0 ≤ rationalShare bid opponent ∧ rationalShare bid opponent ≤ 1 := by
  unfold rationalShare
  split_ifs <;> norm_num

theorem rationalShare_tie (bid : ℚ) : rationalShare bid bid = 1 / 2 := by simp [rationalShare]

theorem rationalShare_constant_sum (bid opponent : ℚ) :
    rationalShare bid opponent + rationalShare opponent bid = 1 := by
  have he := share_constant_sum (bid : ℝ) (opponent : ℝ)
  rw [← rationalShare_real, ← rationalShare_real] at he
  exact_mod_cast he

def opposingLocalLoss {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m) (opponent : ℚ) : Fin (sizes selected) → ℚ :=
  fun code => rationalShare opponent (bids selected code)

theorem opposingLocalLoss_real {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m) (opponent : ℚ)
    (code : Fin (sizes selected)) :
    (opposingLocalLoss bids selected opponent code : ℝ) =
      share (opponent : ℝ) (bids selected code : ℝ) := rationalShare_real _ _

theorem opposingLocalLoss_unit {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (selected : Fin m) (opponent : ℚ)
    (code : Fin (sizes selected)) :
    0 ≤ opposingLocalLoss bids selected opponent code ∧ opposingLocalLoss bids selected opponent code ≤ 1 :=
  rationalShare_unit _ _

end SparseMW
end Blotto
