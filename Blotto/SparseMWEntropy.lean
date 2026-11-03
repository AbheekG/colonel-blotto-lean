import Blotto.SparseMWPotential

/-! Exact finite normalized multiplicative updates and comparator relative
entropy changes. These are the deterministic entropy ingredients used by
R135 §3 and inherited by R136/R143; the stochastic auxiliary process and the
sharp product-norm regret constants are separate obligations. -/

namespace Blotto
open scoped BigOperators Classical

namespace SparseMW

noncomputable def normalizer {n : ℕ} (probability loss : Fin n → ℝ) (eta : ℝ) : ℝ :=
  ∑ i, probability i * Real.exp (-eta * loss i)

noncomputable def normalizedUpdate {n : ℕ} (probability loss : Fin n → ℝ) (eta : ℝ) : Fin n → ℝ :=
  fun i => probability i * Real.exp (-eta * loss i) / normalizer probability loss eta

noncomputable def relativeEntropy {n : ℕ} (comparator probability : Fin n → ℝ) : ℝ :=
  ∑ i, comparator i * (Real.log (comparator i) - Real.log (probability i))

theorem normalizer_positive {n : ℕ} (probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1) :
    0 < normalizer probability loss eta := by
  have hn : Nonempty (Fin n) := by
    by_contra he
    have hzero : n = 0 := by
      by_contra hz
      exact he ⟨⟨0, Nat.pos_of_ne_zero hz⟩⟩
    subst n
    simp at hs
  obtain ⟨i⟩ := hn
  exact Finset.sum_pos (fun j _ => mul_pos (hp j) (Real.exp_pos _)) ⟨i, Finset.mem_univ i⟩

theorem normalizedUpdate_positive {n : ℕ} (probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1) (i : Fin n) :
    0 < normalizedUpdate probability loss eta i :=
  div_pos (mul_pos (hp i) (Real.exp_pos _)) (normalizer_positive probability loss eta hp hs)

theorem normalizedUpdate_sum {n : ℕ} (probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1) :
    (∑ i, normalizedUpdate probability loss eta i) = 1 := by
  unfold normalizedUpdate
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (normalizer_positive probability loss eta hp hs))

theorem normalizedUpdate_log {n : ℕ} (probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1) (i : Fin n) :
    Real.log (normalizedUpdate probability loss eta i) =
      Real.log (probability i) - eta * loss i - Real.log (normalizer probability loss eta) := by
  unfold normalizedUpdate
  rw [Real.log_div (ne_of_gt (mul_pos (hp i) (Real.exp_pos _)))
    (ne_of_gt (normalizer_positive probability loss eta hp hs)),
    Real.log_mul (ne_of_gt (hp i)) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem relativeEntropy_step_identity {n : ℕ} (comparator probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (hu : ∑ i, comparator i = 1) :
    relativeEntropy comparator (normalizedUpdate probability loss eta) - relativeEntropy comparator probability =
      Real.log (normalizer probability loss eta) + eta * ∑ i, comparator i * loss i := by
  unfold relativeEntropy
  rw [← Finset.sum_sub_distrib]
  simp_rw [normalizedUpdate_log probability loss eta hp hs]
  have he : ∀ i,
      comparator i * (Real.log (comparator i) -
        (Real.log (probability i) - eta * loss i - Real.log (normalizer probability loss eta))) -
      comparator i * (Real.log (comparator i) - Real.log (probability i)) =
        comparator i * Real.log (normalizer probability loss eta) + eta * (comparator i * loss i) := by
    intro i
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hu, one_mul]

theorem exponential_quadratic_upper (x : ℝ) (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + (3 / 4 : ℝ) * x ^ 2 := by
  have he := (abs_le.mp (Real.exp_bound hx (n := 2) (by decide))).2
  norm_num [Finset.sum_range_succ] at he
  linarith

theorem log_normalizer_quadratic {n : ℕ} (probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (hscaled : ∀ i, |eta * loss i| ≤ 1) :
    Real.log (normalizer probability loss eta) ≤
      -eta * (∑ i, probability i * loss i) +
        (3 / 4 : ℝ) * eta ^ 2 * (∑ i, probability i * loss i ^ 2) := by
  have hZ := normalizer_positive probability loss eta hp hs
  have hlog := Real.log_le_sub_one_of_pos hZ
  have hsum : normalizer probability loss eta ≤
      1 - eta * (∑ i, probability i * loss i) +
        (3 / 4 : ℝ) * eta ^ 2 * (∑ i, probability i * loss i ^ 2) := by
    calc
      _ ≤ ∑ i, probability i * (1 - eta * loss i + (3 / 4 : ℝ) * (eta * loss i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        have he := exponential_quadratic_upper (-eta * loss i)
          (by simpa only [neg_mul, abs_neg] using hscaled i)
        exact mul_le_mul_of_nonneg_left (by nlinarith [he]) (hp i).le
      _ = _ := by
        simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hs]
        have hlinear : (∑ i, probability i * (eta * loss i)) = eta * ∑ i, probability i * loss i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hquad : (∑ i, probability i * ((3 / 4 : ℝ) * (eta * loss i) ^ 2)) =
            (3 / 4 : ℝ) * eta ^ 2 * ∑ i, probability i * loss i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hlinear, hquad]
  linarith

theorem relativeEntropy_step_quadratic {n : ℕ} (comparator probability loss : Fin n → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 < probability i) (hs : ∑ i, probability i = 1)
    (hu : ∑ i, comparator i = 1) (hscaled : ∀ i, |eta * loss i| ≤ 1) :
    eta * (∑ i, (probability i - comparator i) * loss i) ≤
      relativeEntropy comparator probability - relativeEntropy comparator (normalizedUpdate probability loss eta) +
        (3 / 4 : ℝ) * eta ^ 2 * (∑ i, probability i * loss i ^ 2) := by
  have he := relativeEntropy_step_identity comparator probability loss eta hp hs hu
  have hb := log_normalizer_quadratic probability loss eta hp hs hscaled
  have hsum : (∑ i, (probability i - comparator i) * loss i) =
      (∑ i, probability i * loss i) - ∑ i, comparator i * loss i := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  linarith

theorem rational_multiplier_normalized_update {n : ℕ} (weights multipliers : Fin n → ℚ)
    (eta : ℝ) (heta : eta ≠ 0) (hm : ∀ i, 0 < multipliers i) :
    normalizedUpdate (fun i => (weights i : ℝ))
      (fun i => effectiveLoss eta (multipliers i : ℝ)) eta =
      fun i => (weights i : ℝ) * (multipliers i : ℝ) /
        (∑ j, (weights j : ℝ) * (multipliers j : ℝ)) := by
  have he : ∀ i, Real.exp (-eta * effectiveLoss eta (multipliers i : ℝ)) = (multipliers i : ℝ) := by
    intro i
    exact effectiveLoss_exact heta (by exact_mod_cast hm i)
  funext i
  simp only [normalizedUpdate, normalizer, he]

/- This coarse deterministic telescope retains its proved 3/4 coefficient.
It does not certify R135's sharper 1/2 product-norm constant. -/
theorem finite_relativeEntropy_regret {n : ℕ} (comparator : Fin n → ℝ)
    (probability loss : ℕ → Fin n → ℝ) (eta : ℝ)
    (hu : ∑ i, comparator i = 1)
    (hp : ∀ t i, 0 < probability t i) (hs : ∀ t, ∑ i, probability t i = 1)
    (hscaled : ∀ t i, |eta * loss t i| ≤ 1)
    (hstep : ∀ t, probability (t + 1) = normalizedUpdate (probability t) (loss t) eta)
    (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i, (probability t i - comparator i) * loss t i) ≤
      relativeEntropy comparator (probability 0) - relativeEntropy comparator (probability T) +
        (3 / 4 : ℝ) * eta ^ 2 *
          (∑ t ∈ Finset.range T, ∑ i, probability t i * loss t i ^ 2) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have he := relativeEntropy_step_quadratic comparator (probability T) (loss T) eta
      (hp T) (hs T) hu (hscaled T)
    rw [← hstep T] at he
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith

theorem rational_rounded_relativeEntropy_step {n : ℕ} (comparator probability : Fin n → ℝ)
    (multipliers : Fin n → ℚ) (eta : ℝ) (heta : eta ≠ 0)
    (hm : ∀ i, 0 < multipliers i) (hp : ∀ i, 0 < probability i)
    (hs : ∑ i, probability i = 1) (hu : ∑ i, comparator i = 1) :
    relativeEntropy comparator
        (fun i => probability i * (multipliers i : ℝ) / (∑ j, probability j * (multipliers j : ℝ))) -
      relativeEntropy comparator probability =
        Real.log (∑ j, probability j * (multipliers j : ℝ)) +
          eta * ∑ i, comparator i * effectiveLoss eta (multipliers i : ℝ) := by
  have he : ∀ i, Real.exp (-eta * effectiveLoss eta (multipliers i : ℝ)) = (multipliers i : ℝ) := by
    intro i
    exact effectiveLoss_exact heta (by exact_mod_cast hm i)
  have ht := relativeEntropy_step_identity comparator probability
    (fun i => effectiveLoss eta (multipliers i : ℝ)) eta hp hs hu
  have hupdate : normalizedUpdate probability (fun i => effectiveLoss eta (multipliers i : ℝ)) eta =
      fun i => probability i * (multipliers i : ℝ) / (∑ j, probability j * (multipliers j : ℝ)) := by
    funext i
    simp only [normalizedUpdate, normalizer, he]
  rw [hupdate] at ht
  simpa only [normalizer, he] using ht

end SparseMW
end Blotto
