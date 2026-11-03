import Blotto.SparseMWSharpPotential

/-! Native rational coordinate multipliers induce exactly the real normalized
entropy update. The deterministic sharp regret applies to the actual rational
weight trajectory; signed noise and stochastic/security composition remain open. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

def multiplyWeights {n : ℕ} (weights multipliers : Fin n → ℚ) : Fin n → ℚ :=
  fun i => weights i * multipliers i

def normalizeQ {n : ℕ} (weights : Fin n → ℚ) : Fin n → ℚ :=
  fun i => weights i / ∑ j, weights j

noncomputable def normalizedReal {n : ℕ} (weights : Fin n → ℚ) : Fin n → ℝ :=
  fun i => (normalizeQ weights i : ℝ)

theorem weightSum_positive {n : ℕ} (hn : 0 < n) (weights : Fin n → ℚ)
    (hw : ∀ i, 0 < weights i) : 0 < ∑ i, weights i :=
  Finset.sum_pos (fun i _ => hw i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem normalizeQ_positive {n : ℕ} (hn : 0 < n) (weights : Fin n → ℚ)
    (hw : ∀ i, 0 < weights i) (i : Fin n) : 0 < normalizeQ weights i :=
  div_pos (hw i) (weightSum_positive hn weights hw)

theorem normalizeQ_sum {n : ℕ} (hn : 0 < n) (weights : Fin n → ℚ)
    (hw : ∀ i, 0 < weights i) : (∑ i, normalizeQ weights i) = 1 := by
  unfold normalizeQ
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, mul_inv_cancel₀ (ne_of_gt (weightSum_positive hn weights hw))]

theorem normalizedReal_positive {n : ℕ} (hn : 0 < n) (weights : Fin n → ℚ)
    (hw : ∀ i, 0 < weights i) (i : Fin n) : 0 < normalizedReal weights i := by
  unfold normalizedReal
  exact_mod_cast normalizeQ_positive hn weights hw i

theorem normalizedReal_sum {n : ℕ} (hn : 0 < n) (weights : Fin n → ℚ)
    (hw : ∀ i, 0 < weights i) : (∑ i, normalizedReal weights i) = 1 := by
  unfold normalizedReal
  exact_mod_cast normalizeQ_sum hn weights hw

theorem normalizedReal_update {n : ℕ} (hn : 0 < n) (weights multipliers : Fin n → ℚ)
    (hw : ∀ i, 0 < weights i) (hm : ∀ i, 0 < multipliers i)
    (eta : ℝ) (heta : eta ≠ 0) :
    normalizedReal (multiplyWeights weights multipliers) =
      normalizedUpdate (normalizedReal weights) (fun i => effectiveLoss eta (multipliers i : ℝ)) eta := by
  have hsum : (0 : ℝ) < ∑ i, (weights i : ℝ) := by exact_mod_cast weightSum_positive hn weights hw
  have hmExp : ∀ i, Real.exp (-eta * effectiveLoss eta (multipliers i : ℝ)) = (multipliers i : ℝ) := by
    intro i
    exact effectiveLoss_exact heta (by exact_mod_cast hm i)
  have hden : (∑ i, ((weights i : ℝ) / ∑ j, (weights j : ℝ)) * (multipliers i : ℝ)) =
      (∑ i, (weights i : ℝ) * (multipliers i : ℝ)) / (∑ j, (weights j : ℝ)) := by
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  funext i
  unfold normalizedReal normalizeQ multiplyWeights normalizedUpdate normalizer
  simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_mul, hmExp]
  rw [hden]
  field_simp

theorem selected_update_multiply {n : ℕ} (weights : Fin n → ℚ) (selected : Fin n) (multiplier : ℚ) :
    update weights selected multiplier = multiplyWeights weights (fun i => if i = selected then multiplier else 1) := by
  funext i
  by_cases hi : i = selected
  · subst i
    simp only [update_selected, multiplyWeights, ite_true]
  · rw [update_other weights selected i multiplier hi]
    simp only [multiplyWeights, hi, ite_false, mul_one]

def multiplierTrajectory {n : ℕ} (multipliers : ℕ → Fin n → ℚ) : ℕ → Fin n → ℚ
  | 0 => fun _ => 1
  | t + 1 => multiplyWeights (multiplierTrajectory multipliers t) (multipliers t)

theorem multiplierTrajectory_positive {n : ℕ} (multipliers : ℕ → Fin n → ℚ)
    (hm : ∀ t i, 0 < multipliers t i) (t : ℕ) : ∀ i, 0 < multiplierTrajectory multipliers t i := by
  induction t with
  | zero => intro i; norm_num [multiplierTrajectory]
  | succ t ih => intro i; exact mul_pos (ih i) (hm t i)

theorem normalizedTrajectory_uniform {n : ℕ} (multipliers : ℕ → Fin n → ℚ) :
    normalizedReal (multiplierTrajectory multipliers 0) = fun _ : Fin n => 1 / (n : ℝ) := by
  funext i
  simp [normalizedReal, normalizeQ, multiplierTrajectory]

theorem native_uniform_sharp_regret {n : ℕ} (hn : 0 < n) (comparator : Fin n → ℝ)
    (multipliers : ℕ → Fin n → ℚ) (eta : ℝ) (heta : 0 < eta)
    (hu : ∀ i, 0 ≤ comparator i) (hsu : ∑ i, comparator i = 1)
    (hm : ∀ t i, 0 < multipliers t i) (hmUpper : ∀ t i, multipliers t i ≤ 1) (T : ℕ) :
    eta * (∑ t ∈ Finset.range T, ∑ i,
      (normalizedReal (multiplierTrajectory multipliers t) i - comparator i) *
        effectiveLoss eta (multipliers t i : ℝ)) ≤
      Real.log n + (eta ^ 2 / 2) * (∑ t ∈ Finset.range T, ∑ i,
        normalizedReal (multiplierTrajectory multipliers t) i *
          effectiveLoss eta (multipliers t i : ℝ) ^ 2) := by
  apply finite_uniform_sharp_regret hn comparator
    (fun t => normalizedReal (multiplierTrajectory multipliers t))
    (fun t i => effectiveLoss eta (multipliers t i : ℝ)) eta hu hsu
  · intro t i
    exact normalizedReal_positive hn _ (multiplierTrajectory_positive multipliers hm t) i
  · intro t
    exact normalizedReal_sum hn _ (multiplierTrajectory_positive multipliers hm t)
  · exact normalizedTrajectory_uniform multipliers
  · exact heta.le
  · intro t i
    exact rounded_effectiveLoss_nonnegative heta (by exact_mod_cast hm t i) (by exact_mod_cast hmUpper t i)
  · intro t
    exact normalizedReal_update hn _ _ (multiplierTrajectory_positive multipliers hm t) (hm t) eta (ne_of_gt heta)

end SparseMW
end Blotto
