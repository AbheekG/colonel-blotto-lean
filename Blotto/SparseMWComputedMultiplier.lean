import Blotto.RationalExpApproximation
import Blotto.SparseMWSharpPotential

/-! Computed Taylor-plus-rounding multipliers satisfy the sparse update's
positivity, downward and effective-loss contracts. The source's stochastic
learner, stored-word growth and full computational costs remain separate. -/

namespace Blotto
namespace SparseMW

theorem expMultiplierNative_unit (x theta : ℚ)
    (hx : 0 ≤ x ∧ x ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    0 < expMultiplierNative x theta ∧ expMultiplierNative x theta ≤ 1 := by
  have hc := expMultiplierNative_certificate x theta hx ht
  have hxR : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx.1
  have he : Real.exp (-(x : ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hh := hc.2.2.trans he
  exact ⟨hc.1, Rat.cast_le.mp (by simpa only [Rat.cast_one] using hh)⟩

theorem computedMultiplier_effectiveLoss (eta loss theta : ℚ)
    (heta : 0 < eta) (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4)
    (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    (loss : ℝ) ≤ effectiveLoss (eta : ℝ) (expMultiplierNative (eta * loss) theta : ℝ) ∧
    effectiveLoss (eta : ℝ) (expMultiplierNative (eta * loss) theta : ℝ) ≤
      (loss : ℝ) + 2 * (theta : ℝ) / (eta : ℝ) := by
  rw [expMultiplierNative_refines]
  exact expMultiplier_effectiveLoss eta loss theta heta hx ht

theorem computedMultiplier_loss_unit (eta loss theta : ℚ)
    (heta : 0 < eta) (hl : 0 ≤ loss ∧ loss ≤ 1) (hetaCap : eta ≤ 1 / 4)
    (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    0 ≤ effectiveLoss (eta : ℝ) (expMultiplierNative (eta * loss) theta : ℝ) ∧
    effectiveLoss (eta : ℝ) (expMultiplierNative (eta * loss) theta : ℝ) ≤
      1 + 2 * (theta : ℝ) / (eta : ℝ) := by
  have hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4 :=
    ⟨mul_nonneg heta.le hl.1, (mul_le_of_le_one_right heta.le hl.2).trans hetaCap⟩
  have hc := computedMultiplier_effectiveLoss eta loss theta heta hx ht
  have hl0 : (0 : ℝ) ≤ (loss : ℝ) := by exact_mod_cast hl.1
  have hl1 : (loss : ℝ) ≤ 1 := by exact_mod_cast hl.2
  constructor <;> linarith [hc.1, hc.2]

def computedSparseUpdate {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m)
    (eta loss theta : ℚ) : Fin m → ℚ :=
  update weights selected (expMultiplierNative (eta * loss) theta)

theorem computedSparseUpdate_positive {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m)
    (eta loss theta : ℚ) (hw : ∀ j, 0 < weights j)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    ∀ j, 0 < computedSparseUpdate weights selected eta loss theta j :=
  update_positive weights selected _ hw (expMultiplierNative_unit _ _ hx ht).1

theorem computedSparseUpdate_decreases {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m)
    (eta loss theta : ℚ) (hw : ∀ j, 0 ≤ weights j)
    (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    ∀ j, computedSparseUpdate weights selected eta loss theta j ≤ weights j :=
  update_decreases weights selected _ hw (expMultiplierNative_unit _ _ hx ht).2

theorem computedSparseUpdate_product {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m)
    (eta loss theta : ℚ) :
    (∏ j, computedSparseUpdate weights selected eta loss theta j) =
      (∏ j, weights j) * expMultiplierNative (eta * loss) theta :=
  update_product weights selected _

end SparseMW
end Blotto
