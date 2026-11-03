import Blotto.SparseMWComputedRegret

/-! Exact finite histories with adaptive transition probabilities. Conditional
mean-zero noise cancels against every predictable test, including an auxiliary
iterate minus the actual iterate; no maximizing comparator is declared unbiased.
Connecting these transitions to the learner's native samplers remains separate. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

/-- Newest observations occur first. Transition laws may depend on all past data. -/
noncomputable def historyMass {a : ℕ} (transition : List (Fin a) → Fin a → ℝ) : List (Fin a) → ℝ
  | [] => 1
  | x :: past => historyMass transition past * transition past x

def histories (a : ℕ) : ℕ → List (List (Fin a))
  | 0 => [[]]
  | t + 1 => (histories a t).flatMap (fun past => (List.finRange a).map (fun x => x :: past))

noncomputable def historyMean {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (t : ℕ) (f : List (Fin a) → ℝ) : ℝ :=
  ((histories a t).map (fun past => historyMass transition past * f past)).sum

theorem historyMass_nonnegative {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (past : List (Fin a)) :
    0 ≤ historyMass transition past := by
  induction past with
  | nil => norm_num [historyMass]
  | cons x past ih => exact mul_nonneg ih (hp past x)

theorem historyMean_zero {a : ℕ} (transition : List (Fin a) → Fin a → ℝ) (f : List (Fin a) → ℝ) :
    historyMean transition 0 f = f [] := by simp [historyMean, histories, historyMass]

theorem histories_length {a t : ℕ} (past : List (Fin a)) (h : past ∈ histories a t) :
    past.length = t := by
  induction t generalizing past with
  | zero =>
    have he : past = [] := by simpa only [histories, List.mem_singleton] using h
    subst past
    rfl
  | succ t ih =>
    rw [histories] at h
    obtain ⟨previous, hprevious, hx⟩ := List.mem_flatMap.mp h
    obtain ⟨observed, _, he⟩ := List.mem_map.mp hx
    subst past
    simp only [List.length_cons]
    exact congrArg Nat.succ (ih previous hprevious)

theorem historyMean_succ {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (t : ℕ) (f : List (Fin a) → ℝ) :
    historyMean transition (t + 1) f =
      historyMean transition t (fun past => ∑ x, transition past x * f (x :: past)) := by
  unfold historyMean
  change (((histories a t).flatMap (fun past => (List.finRange a).map (fun x => x :: past))).map
    (fun past => historyMass transition past * f past)).sum = _
  rw [List.map_flatMap]
  rw [List.flatMap_def, List.sum_flatten]
  simp only [List.map_map, Function.comp_def, historyMass]
  apply congrArg List.sum
  apply List.map_congr_left
  intro past _
  simp only [mul_assoc]
  rw [List.sum_map_mul_left, ← Fin.sum_univ_def]

theorem historyMean_constant {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (hs : ∀ past, ∑ x, transition past x = 1) (t : ℕ) (c : ℝ) :
    historyMean transition t (fun _ => c) = c := by
  induction t with
  | zero => exact historyMean_zero transition _
  | succ t ih =>
    rw [historyMean_succ]
    simp only [← Finset.sum_mul, hs, one_mul]
    exact ih

theorem historyMean_add {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (t : ℕ) (f g : List (Fin a) → ℝ) :
    historyMean transition t (fun past => f past + g past) =
      historyMean transition t f + historyMean transition t g := by
  unfold historyMean
  simp only [mul_add, List.sum_map_add]

theorem historyMean_mul {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (t : ℕ) (c : ℝ) (f : List (Fin a) → ℝ) :
    historyMean transition t (fun past => c * f past) = c * historyMean transition t f := by
  unfold historyMean
  have he : ∀ past, historyMass transition past * (c * f past) =
      c * (historyMass transition past * f past) := by intro past; ring
  simp only [he, List.sum_map_mul_left]

theorem historyMean_monotone {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (t : ℕ) (f g : List (Fin a) → ℝ)
    (h : ∀ past, f past ≤ g past) : historyMean transition t f ≤ historyMean transition t g := by
  unfold historyMean
  apply List.sum_le_sum
  intro past _
  exact mul_le_mul_of_nonneg_left (h past) (historyMass_nonnegative transition hp past)

theorem historyMean_monotone_at_length {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (t : ℕ) (f g : List (Fin a) → ℝ)
    (h : ∀ past, past.length = t → f past ≤ g past) :
    historyMean transition t f ≤ historyMean transition t g := by
  unfold historyMean
  apply List.sum_le_sum
  intro past hmem
  exact mul_le_mul_of_nonneg_left (h past (histories_length past hmem))
    (historyMass_nonnegative transition hp past)

noncomputable def newestNoisePairing {a n : ℕ} (noise : List (Fin a) → Fin a → Fin n → ℝ)
    (test : List (Fin a) → Fin n → ℝ) : List (Fin a) → ℝ
  | [] => 0
  | x :: past => ∑ i, noise past x i * test past i

theorem predictable_noise_mean_zero {a n : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (noise : List (Fin a) → Fin a → Fin n → ℝ)
    (hz : ∀ past i, ∑ x, transition past x * noise past x i = 0)
    (test : List (Fin a) → Fin n → ℝ) (t : ℕ) :
    historyMean transition (t + 1) (newestNoisePairing noise test) = 0 := by
  rw [historyMean_succ]
  have hconditional : ∀ past, (∑ x, transition past x * newestNoisePairing noise test (x :: past)) = 0 := by
    intro past
    simp only [newestNoisePairing, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hpoint : ∀ i, (∑ x, transition past x * (noise past x i * test past i)) = 0 := by
      intro i
      calc
        _ = (∑ x, transition past x * noise past x i) * test past i := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = 0 := by rw [hz, zero_mul]
    simp only [hpoint, Finset.sum_const_zero]
  simp only [hconditional]
  unfold historyMean
  simp

noncomputable def conditionalDirection {a n : ℕ}
    (transition : List (Fin a) → Fin a → ℝ)
    (empirical : List (Fin a) → Fin a → Fin n → ℝ) (past : List (Fin a)) (i : Fin n) : ℝ :=
  ∑ x, transition past x * empirical past x i

theorem conditionalDirection_noise_mean_zero {a n : ℕ}
    (transition : List (Fin a) → Fin a → ℝ)
    (hs : ∀ past, ∑ x, transition past x = 1)
    (empirical : List (Fin a) → Fin a → Fin n → ℝ) (past : List (Fin a)) (i : Fin n) :
    (∑ x, transition past x * (empirical past x i - conditionalDirection transition empirical past i)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul,
    conditionalDirection, sub_self]

theorem conditionalDirection_unit {a n : ℕ}
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (hs : ∀ past, ∑ x, transition past x = 1)
    (empirical : List (Fin a) → Fin a → Fin n → ℝ)
    (hl : ∀ past x i, 0 ≤ empirical past x i ∧ empirical past x i ≤ 1)
    (past : List (Fin a)) (i : Fin n) :
    0 ≤ conditionalDirection transition empirical past i ∧ conditionalDirection transition empirical past i ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp past x) (hl past x i).1)
  · calc
      _ ≤ ∑ x, transition past x :=
        Finset.sum_le_sum (fun x _ => mul_le_of_le_one_right (hp past x) (hl past x i).2)
      _ = 1 := hs past

theorem conditionalDirection_noise_bound {a n : ℕ}
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (hs : ∀ past, ∑ x, transition past x = 1)
    (empirical : List (Fin a) → Fin a → Fin n → ℝ)
    (hl : ∀ past x i, 0 ≤ empirical past x i ∧ empirical past x i ≤ 1)
    (past : List (Fin a)) (x : Fin a) (i : Fin n) :
    |empirical past x i - conditionalDirection transition empirical past i| ≤ 1 := by
  have he := conditionalDirection_unit transition hp hs empirical hl past i
  rw [abs_le]
  constructor <;> linarith [(hl past x i).1, (hl past x i).2, he.1, he.2]

noncomputable def accumulatedNoise {a n : ℕ} (noise : List (Fin a) → Fin a → Fin n → ℝ)
    (test : List (Fin a) → Fin n → ℝ) : List (Fin a) → ℝ
  | [] => 0
  | x :: past => accumulatedNoise noise test past + ∑ i, noise past x i * test past i

theorem historyMean_predictable_extension {a : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (hs : ∀ past, ∑ x, transition past x = 1) (t : ℕ) (f : List (Fin a) → ℝ) :
    historyMean transition (t + 1) (fun full => f full.tail) = historyMean transition t f := by
  rw [historyMean_succ]
  simp only [List.tail_cons, ← Finset.sum_mul, hs, one_mul]

theorem accumulated_noise_mean_zero {a n : ℕ} (transition : List (Fin a) → Fin a → ℝ)
    (hs : ∀ past, ∑ x, transition past x = 1)
    (noise : List (Fin a) → Fin a → Fin n → ℝ)
    (hz : ∀ past i, ∑ x, transition past x * noise past x i = 0)
    (test : List (Fin a) → Fin n → ℝ) (t : ℕ) :
    historyMean transition t (accumulatedNoise noise test) = 0 := by
  induction t with
  | zero => simp [historyMean_zero, accumulatedNoise]
  | succ t ih =>
    have he : accumulatedNoise noise test = fun full =>
        accumulatedNoise noise test full.tail + newestNoisePairing noise test full := by
      funext full
      cases full with
      | nil => simp [accumulatedNoise, newestNoisePairing]
      | cons x past => rfl
    rw [he, historyMean_add, historyMean_predictable_extension transition hs,
      predictable_noise_mean_zero transition noise hz, add_zero]
    exact ih

theorem accumulated_auxiliary_actual_cancellation {a n : ℕ}
    (transition : List (Fin a) → Fin a → ℝ)
    (hs : ∀ past, ∑ x, transition past x = 1)
    (noise : List (Fin a) → Fin a → Fin n → ℝ)
    (hz : ∀ past i, ∑ x, transition past x * noise past x i = 0)
    (auxiliary actual : List (Fin a) → Fin n → ℝ) (t : ℕ) :
    historyMean transition t (accumulatedNoise noise (fun past i => auxiliary past i - actual past i)) = 0 :=
  accumulated_noise_mean_zero transition hs noise hz _ t

end SparseMW
end Blotto
