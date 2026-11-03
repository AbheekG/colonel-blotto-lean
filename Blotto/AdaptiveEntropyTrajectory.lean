import Blotto.StochasticUniformRegret
import Blotto.SparseMWSignedPotential

/-! The proof-only auxiliary entropy process is an actual history recurrence.
Every path refines finite normalized updates; signed regret can therefore be
used uniformly without assuming an auxiliary prox inequality as an oracle. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

noncomputable def entropyHistory {a n : ℕ}
    (direction : List (Fin a) → Fin a → Fin n → ℝ) (eta : ℝ) : List (Fin a) → Fin n → ℝ
  | [] => fun _ => 1 / (n : ℝ)
  | x :: past => normalizedUpdate (entropyHistory direction eta past) (direction past x) eta

theorem entropyHistory_positive {a n : ℕ} (hn : 0 < n)
    (direction : List (Fin a) → Fin a → Fin n → ℝ) (eta : ℝ) (past : List (Fin a)) :
    (∀ i, 0 < entropyHistory direction eta past i) ∧
      (∑ i, entropyHistory direction eta past i) = 1 := by
  induction past with
  | nil =>
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · intro i; exact one_div_pos.mpr hnR
    · simp [entropyHistory, ne_of_gt hnR]
  | cons x past ih =>
    exact ⟨normalizedUpdate_positive _ _ eta ih.1 ih.2,
      normalizedUpdate_sum _ _ eta ih.1 ih.2⟩

theorem entropyHistory_uniform_regret {a n : ℕ} (hn : 0 < n)
    (direction : List (Fin a) → Fin a → Fin n → ℝ) (eta cap : ℝ)
    (heta : 0 ≤ eta) (hcap : ∀ past x i, |direction past x i| ≤ cap)
    (comparator : Fin n → ℝ) (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (past : List (Fin a)) :
    eta * cumulativePairing direction (entropyHistory direction eta) comparator past ≤
      Real.log n + (eta ^ 2 / 2) * past.length * cap ^ 2 := by
  have htelescope : ∀ past : List (Fin a),
      eta * cumulativePairing direction (entropyHistory direction eta) comparator past ≤
        relativeEntropy comparator (entropyHistory direction eta []) -
          relativeEntropy comparator (entropyHistory direction eta past) +
            (eta ^ 2 / 2) * past.length * cap ^ 2 := by
    intro past
    induction past with
    | nil => simp [cumulativePairing]
    | cons x past ih =>
      have hp := entropyHistory_positive hn direction eta past
      have he := relativeEntropy_step_signed_sharp comparator (entropyHistory direction eta past)
        (direction past x) eta cap hp.1 hp.2 hsu heta (hcap past x)
      change eta * (∑ i, (entropyHistory direction eta past i - comparator i) * direction past x i) ≤
        relativeEntropy comparator (entropyHistory direction eta past) -
          relativeEntropy comparator (entropyHistory direction eta (x :: past)) + eta ^ 2 * cap ^ 2 / 2 at he
      have hpair : (∑ i, direction past x i * (entropyHistory direction eta past i - comparator i)) =
          ∑ i, (entropyHistory direction eta past i - comparator i) * direction past x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [cumulativePairing, hpair, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith
  have he := htelescope past
  have hp := entropyHistory_positive hn direction eta past
  have hnonnegative := relativeEntropy_nonnegative comparator (entropyHistory direction eta past) hu hsu hp.1 hp.2
  have hstart := relativeEntropy_uniform_bound hn comparator hu hsu
  change relativeEntropy comparator (entropyHistory direction eta []) ≤ Real.log n at hstart
  linarith

def rationalHistory {a n : ℕ}
    (multipliers : List (Fin a) → Fin a → Fin n → ℚ) : List (Fin a) → Fin n → ℚ
  | [] => fun _ => 1
  | x :: past => multiplyWeights (rationalHistory multipliers past) (multipliers past x)

theorem rationalHistory_positive {a n : ℕ}
    (multipliers : List (Fin a) → Fin a → Fin n → ℚ)
    (hm : ∀ past x i, 0 < multipliers past x i) (past : List (Fin a)) :
    ∀ i, 0 < rationalHistory multipliers past i := by
  induction past with
  | nil => intro i; norm_num [rationalHistory]
  | cons x past ih => intro i; exact mul_pos (ih i) (hm past x i)

theorem rationalHistory_effective_regret {a n : ℕ} (hn : 0 < n)
    (multipliers : List (Fin a) → Fin a → Fin n → ℚ) (eta cap : ℝ) (heta : 0 < eta)
    (hm : ∀ past x i, 0 < multipliers past x i)
    (hmUpper : ∀ past x i, multipliers past x i ≤ 1)
    (hcap : ∀ past x i, effectiveLoss eta (multipliers past x i : ℝ) ≤ cap)
    (comparator : Fin n → ℝ) (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (past : List (Fin a)) :
    eta * cumulativePairing (fun h x i => effectiveLoss eta (multipliers h x i : ℝ))
      (fun h => normalizedReal (rationalHistory multipliers h)) comparator past ≤
        Real.log n + (eta ^ 2 / 2) * past.length * cap ^ 2 := by
  let probability := fun h => normalizedReal (rationalHistory multipliers h)
  let effective := fun h x i => effectiveLoss eta (multipliers h x i : ℝ)
  have hp : ∀ h, (∀ i, 0 < probability h i) ∧ (∑ i, probability h i) = 1 := by
    intro h
    exact ⟨normalizedReal_positive hn _ (rationalHistory_positive multipliers hm h),
      normalizedReal_sum hn _ (rationalHistory_positive multipliers hm h)⟩
  have he : ∀ h x i, 0 ≤ effective h x i ∧ effective h x i ≤ cap := by
    intro h x i
    exact ⟨rounded_effectiveLoss_nonnegative heta (by exact_mod_cast hm h x i)
      (by exact_mod_cast hmUpper h x i), hcap h x i⟩
  have htelescope : ∀ past : List (Fin a),
      eta * cumulativePairing effective probability comparator past ≤
        relativeEntropy comparator (probability []) - relativeEntropy comparator (probability past) +
          (eta ^ 2 / 2) * past.length * cap ^ 2 := by
    intro past
    induction past with
    | nil => simp [cumulativePairing]
    | cons x past ih =>
      have hstep : probability (x :: past) = normalizedUpdate (probability past) (effective past x) eta :=
        normalizedReal_update hn _ _ (rationalHistory_positive multipliers hm past) (hm past x) eta (ne_of_gt heta)
      have hs := relativeEntropy_step_signed_sharp comparator (probability past) (effective past x)
        eta cap (hp past).1 (hp past).2 hsu heta.le (fun i => by
          rw [abs_of_nonneg (he past x i).1]; exact (he past x i).2)
      rw [← hstep] at hs
      have hpair : (∑ i, effective past x i * (probability past i - comparator i)) =
          ∑ i, (probability past i - comparator i) * effective past x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [cumulativePairing, hpair, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith
  have ht := htelescope past
  have hnonnegative := relativeEntropy_nonnegative comparator (probability past) hu hsu (hp past).1 (hp past).2
  have hstart := relativeEntropy_uniform_bound hn comparator hu hsu
  have hzero : probability [] = fun _ => 1 / (n : ℝ) := by
    funext i
    simp [probability, normalizedReal, normalizeQ, rationalHistory]
  rw [← hzero] at hstart
  exact by linarith

end SparseMW
end Blotto
