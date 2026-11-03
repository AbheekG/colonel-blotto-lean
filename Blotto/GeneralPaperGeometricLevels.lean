import Blotto.SparseMWRationalUpdate
import Blotto.SparseMWSignedPotential

/-! The selected source's exact natural levels and their full-alphabet law.
The law and powers here are a mathematical reference; evaluating the dense
alphabet is not asserted to be the compressed source implementation. Each
signed alphabet is one `Fin n`, normalized once over both signs together.
Weights in this module contain no battlefield-value multiplier.
-/
namespace Blotto.GeneralPaperGeometricLevels
open scoped BigOperators Classical
open SparseMW
set_option autoImplicit false

def levels {n : ℕ} (increment : ℕ → Fin n → ℕ) : ℕ → Fin n → ℕ
  | 0 => fun _ => 0
  | t+1 => fun i => levels increment t i + increment t i

def weights {n : ℕ} (base : ℚ) (increment : ℕ → Fin n → ℕ) (t : ℕ) : Fin n → ℚ :=
  fun i => base ^ levels increment t i

def law {n : ℕ} (base : ℚ) (increment : ℕ → Fin n → ℕ) (t : ℕ) : Fin n → ℚ :=
  normalizeQ (weights base increment t)

noncomputable def probability {n : ℕ} (base : ℚ) (increment : ℕ → Fin n → ℕ)
    (t : ℕ) : Fin n → ℝ := normalizedReal (weights base increment t)

def executedLoss (theta : ℚ) (increment : ℕ) : ℚ := theta / 2 * increment - 2

def geometricBase (eta theta : ℚ) : ℚ := 1 - eta * theta / 2

noncomputable def rate (base theta : ℚ) : ℝ := -2 * Real.log (base : ℝ) / theta

theorem levels_sum {n : ℕ} (increment : ℕ → Fin n → ℕ) (t : ℕ) (i : Fin n) :
    levels increment t i = ∑ k ∈ Finset.range t, increment k i := by
  induction t with
  | zero => simp [levels]
  | succ t ih => simp only [levels, Finset.sum_range_succ, ih]

theorem levels_epoch {n : ℕ} (increment : ℕ → Fin n → ℕ) (start count : ℕ) (i : Fin n) :
    levels increment (start+count) i =
      levels increment start i + levels (fun t => increment (start+t)) count i := by
  induction count with
  | zero => simp [levels]
  | succ count ih =>
    change levels increment (start+count) i + increment (start+count) i =
      levels increment start i + (levels (fun t => increment (start+t)) count i + increment (start+count) i)
    rw [ih, Nat.add_assoc]

theorem levels_bound {n : ℕ} (increment : ℕ → Fin n → ℕ) (bound t : ℕ)
    (h : ∀ s i, increment s i ≤ bound) (i : Fin n) : levels increment t i ≤ t*bound := by
  induction t with
  | zero => simp [levels]
  | succ t ih =>
    simp only [levels]
    have hi := h t i
    nlinarith

theorem weights_step {n : ℕ} (base : ℚ) (increment : ℕ → Fin n → ℕ) (t : ℕ) :
    weights base increment (t+1) =
      multiplyWeights (weights base increment t) (fun i => base ^ increment t i) := by
  funext i
  simp only [weights, levels, pow_add, multiplyWeights]

theorem weights_positive {n : ℕ} (base : ℚ) (hBase : 0 < base)
    (increment : ℕ → Fin n → ℕ) (t : ℕ) (i : Fin n) : 0 < weights base increment t i :=
  pow_pos hBase _

theorem law_positive {n : ℕ} (hn : 0 < n) (base : ℚ) (hBase : 0 < base)
    (increment : ℕ → Fin n → ℕ) (t : ℕ) (i : Fin n) : 0 < law base increment t i :=
  normalizeQ_positive hn _ (weights_positive base hBase increment t) i

theorem law_sum {n : ℕ} (hn : 0 < n) (base : ℚ) (hBase : 0 < base)
    (increment : ℕ → Fin n → ℕ) (t : ℕ) : ∑ i, law base increment t i = 1 :=
  normalizeQ_sum hn _ (weights_positive base hBase increment t)

theorem probability_cast {n : ℕ} (base : ℚ) (increment : ℕ → Fin n → ℕ) (t : ℕ) (i : Fin n) :
    probability base increment t i = (law base increment t i : ℝ) := rfl

theorem probability_positive {n : ℕ} (hn : 0 < n) (base : ℚ) (hBase : 0 < base)
    (increment : ℕ → Fin n → ℕ) (t : ℕ) (i : Fin n) : 0 < probability base increment t i :=
  normalizedReal_positive hn _ (weights_positive base hBase increment t) i

theorem probability_sum {n : ℕ} (hn : 0 < n) (base : ℚ) (hBase : 0 < base)
    (increment : ℕ → Fin n → ℕ) (t : ℕ) : ∑ i, probability base increment t i = 1 :=
  normalizedReal_sum hn _ (weights_positive base hBase increment t)

theorem initial_uniform {n : ℕ} (base : ℚ) (increment : ℕ → Fin n → ℕ) :
    probability base increment 0 = fun _ => 1/(n : ℝ) := by
  funext i
  simp [probability, weights, levels, normalizedReal, normalizeQ]

theorem base_bounds (eta theta : ℚ) (hEta : 0 < eta) (hTheta : 0 < theta)
    (hProduct : eta*theta ≤ 1) : 1/2 ≤ geometricBase eta theta ∧ geometricBase eta theta < 1 := by
  unfold geometricBase
  constructor <;> nlinarith [mul_pos hEta hTheta]

theorem rate_positive (base theta : ℚ) (hBase : 0 < base) (hOne : base < 1)
    (hTheta : 0 < theta) : 0 < rate base theta := by
  have hb : (0 : ℝ) < base := by exact_mod_cast hBase
  have h1 : (base : ℝ) < 1 := by exact_mod_cast hOne
  have ht : (0 : ℝ) < theta := by exact_mod_cast hTheta
  unfold rate
  exact div_pos (mul_pos_of_neg_of_neg (by norm_num) (Real.log_neg hb h1)) ht

theorem effectiveLoss_power (base theta : ℚ) (hBase : 0 < base) (hOne : base < 1)
    (hTheta : 0 < theta) (d : ℕ) :
    effectiveLoss (rate base theta) ((base^d : ℚ) : ℝ) = (executedLoss theta d : ℝ) + 2 := by
  have hr := ne_of_gt (rate_positive base theta hBase hOne hTheta)
  have hb : (0 : ℝ) < base := by exact_mod_cast hBase
  have hl : Real.log (base : ℝ) ≠ 0 := ne_of_lt (Real.log_neg hb (by exact_mod_cast hOne))
  have ht : (theta : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hTheta
  unfold effectiveLoss rate executedLoss
  push_cast
  rw [Real.log_pow]
  field_simp
  <;> ring

theorem probability_step {n : ℕ} (hn : 0 < n) (base theta : ℚ)
    (hBase : 0 < base) (hOne : base < 1) (hTheta : 0 < theta)
    (increment : ℕ → Fin n → ℕ) (t : ℕ) :
    probability base increment (t+1) = normalizedUpdate (probability base increment t)
      (fun i => (executedLoss theta (increment t i) : ℝ)) (rate base theta) := by
  unfold probability
  rw [weights_step]
  rw [normalizedReal_update hn _ _ (weights_positive base hBase increment t)
    (fun i => pow_pos hBase _) _ (ne_of_gt (rate_positive base theta hBase hOne hTheta))]
  simp only [effectiveLoss_power base theta hBase hOne hTheta]
  exact normalizedUpdate_shift _ _ _ 2

theorem executed_increment (theta : ℚ) (hTheta : theta ≠ 0) (d : ℕ) :
    2*(executedLoss theta d+2)/theta = d := by
  unfold executedLoss
  field_simp
  <;> ring

theorem increment_bound (theta : ℚ) (hTheta : 0 < theta) (d : ℕ)
    (hLoss : |executedLoss theta d| ≤ 2) : (d : ℚ) ≤ 8/theta := by
  have he := (abs_le.mp hLoss).2
  unfold executedLoss at he
  apply (le_div_iff₀ hTheta).mpr
  nlinarith

end Blotto.GeneralPaperGeometricLevels
