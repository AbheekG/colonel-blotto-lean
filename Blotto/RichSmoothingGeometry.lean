import Blotto.Segments

/-! Actual positive, coordinate-nonconstant full-budget segments approaching
any full-budget pure allocation with at least two fields. One common uniform
scalar suffices; within-player coordinate dependence is preserved. Zero bids
receive a second-order positive perturbation. Positive-coordinate first-order
directions sum to zero. This is the geometric R33 smoothing construction;
fixed-opponent payoff limits and the minimax/compactness join are separate. -/

namespace Blotto.RichSmoothingGeometry
open scoped BigOperators Classical

noncomputable def active {n : ℕ} (x : Allocation n) : Finset (Fin n) :=
  Finset.univ.filter fun j => 0 < x j

noncomputable def count {n : ℕ} (x : Allocation n) : ℕ := (active x).card

theorem mem_active {n : ℕ} (x : Allocation n) (j : Fin n) : j ∈ active x ↔ 0 < x j := by
  simp [active]

theorem active_nonempty {n : ℕ} (x : Allocation n) (budget : ℝ)
    (hBudget : 0 < budget) (hX : FullBudget budget x) : (active x).Nonempty := by
  by_contra h
  have hEmpty : active x = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hZero : ∀ j, x j = 0 := by
    intro j
    have hNot : ¬0 < x j := by rw [← mem_active, hEmpty]; simp
    exact le_antisymm (le_of_not_gt hNot) (hX.1 j)
  have hSum : (∑ j, x j) = 0 := by simp [hZero]
  linarith [hX.2]

theorem count_positive {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) : 0 < count x :=
  Finset.card_pos.mpr h

theorem count_le {n : ℕ} (x : Allocation n) : count x ≤ n := by
  exact (Finset.card_le_card (Finset.subset_univ (active x))).trans_eq (by simp)

noncomputable def chosen {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) : Fin n :=
  (active x).min' h

theorem chosen_mem {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) : chosen x h ∈ active x :=
  Finset.min'_mem _ _

noncomputable def positiveMinimum {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) : ℝ :=
  (active x).inf' h x

theorem positiveMinimum_positive {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) :
    0 < positiveMinimum x h := by
  apply (Finset.lt_inf'_iff h).mpr
  intro j hj
  exact (mem_active x j).mp hj

theorem positiveMinimum_le {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (j : Fin n) (hj : j ∈ active x) : positiveMinimum x h ≤ x j :=
  Finset.inf'_le x hj

noncomputable def compensation {n : ℕ} (x : Allocation n) : ℝ :=
  (n - count x : ℕ) / (count x : ℝ)

theorem compensation_nonnegative {n : ℕ} (x : Allocation n) : 0 ≤ compensation x :=
  div_nonneg (by positivity) (by positivity)

theorem compensation_count {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) :
    compensation x * count x = (n - count x : ℕ) := by
  unfold compensation
  rw [div_mul_cancel₀ _ (by exact_mod_cast (Nat.ne_of_gt (count_positive x h)))]

theorem compensation_le {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) :
    compensation x ≤ n := by
  have hk : (0 : ℝ) < count x := by exact_mod_cast count_positive x h
  have hk1 : (1 : ℝ) ≤ count x := by exact_mod_cast count_positive x h
  have hn : ((n - count x : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n (count x)
  unfold compensation
  apply (div_le_iff₀ hk).mpr
  nlinarith

theorem sum_if_mem {n : ℕ} (s : Finset (Fin n)) (first second : ℝ) :
    (∑ j, if j ∈ s then first else second) =
      (s.card : ℝ) * first + ((n - s.card : ℕ) : ℝ) * second := by
  rw [Finset.sum_ite]
  have hFirst : Finset.univ.filter (fun j => j ∈ s) = s := by ext j; simp
  have hSecond : Finset.univ.filter (fun j => j ∉ s) = Finset.univ \ s := by ext j; simp
  rw [hFirst, hSecond]
  simp [Finset.card_sdiff]

noncomputable def direction {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (j : Fin n) : ℝ :=
  (if j ∈ active x then 1 else 0) - if j = chosen x h then (count x : ℝ) else 0

noncomputable def correction {n : ℕ} (x : Allocation n) (j : Fin n) : ℝ :=
  if j ∈ active x then compensation x else -1

theorem direction_sum {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) :
    (∑ j, direction x h j) = 0 := by
  unfold direction
  rw [Finset.sum_sub_distrib, sum_if_mem]
  simp [count]

theorem correction_sum {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) :
    (∑ j, correction x j) = 0 := by
  unfold correction
  rw [sum_if_mem]
  have hc := compensation_count x h
  change (count x : ℝ) * compensation x + ((n - count x : ℕ) : ℝ) * (-1) = 0
  nlinarith

theorem direction_chosen {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) :
    direction x h (chosen x h) = 1 - count x := by simp [direction, chosen_mem]

theorem direction_other {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (j : Fin n) (hj : j ∈ active x) (hne : j ≠ chosen x h) : direction x h j = 1 := by
  simp [direction, hj, hne]

theorem inactive_zero {n : ℕ} (x : Allocation n) (hX : ∀ j, 0 ≤ x j)
    (j : Fin n) (hj : j ∉ active x) : x j = 0 := by
  exact le_antisymm (le_of_not_gt (fun hp => hj ((mem_active x j).mpr hp))) (hX j)

theorem direction_inactive {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (j : Fin n) (hj : j ∉ active x) : direction x h j = 0 := by
  have hne : j ≠ chosen x h := by intro he; subst j; exact hj (chosen_mem x h)
  simp [direction, hj, hne]

theorem direction_bounds {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (hn : 2 ≤ n) (j : Fin n) : -(n : ℝ) ≤ direction x h j ∧ direction x h j ≤ n := by
  have hk : (count x : ℝ) ≤ n := by exact_mod_cast count_le x
  have hk0 : (0 : ℝ) ≤ count x := by positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold direction
  split_ifs <;> constructor <;> linarith

noncomputable def radius {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) : ℝ :=
  min (1 / (8 * (n + 1 : ℝ))) (positiveMinimum x h / (8 * (n + 1 : ℝ)))

theorem radius_positive {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) : 0 < radius x h := by
  unfold radius
  exact lt_min (by positivity) (div_pos (positiveMinimum_positive x h) (by positivity))

theorem small_bounds {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (t : ℝ) (ht : 0 < t) (htr : t ≤ radius x h) :
    t ≤ 1 ∧ 8 * (n : ℝ) * t ≤ 1 ∧ 8 * (n : ℝ) * t ≤ positiveMinimum x h := by
  have hd : (0 : ℝ) < 8 * (n + 1 : ℝ) := by positivity
  have hOne := (le_div_iff₀ hd).mp (htr.trans (min_le_left _ _))
  have hMin := (le_div_iff₀ hd).mp (htr.trans (min_le_right _ _))
  have hn : (0 : ℝ) ≤ n := by positivity
  constructor
  · nlinarith
  · constructor <;> nlinarith

noncomputable def lower {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (t : ℝ) : Allocation n :=
  fun j => x j - t * direction x h j - t ^ 2 * correction x j

noncomputable def upper {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (t : ℝ) : Allocation n :=
  fun j => x j + t * direction x h j - 3 * t ^ 2 * correction x j

theorem lower_sum {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (t : ℝ) :
    (∑ j, lower x h t j) = ∑ j, x j := by
  unfold lower
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, direction_sum x h, correction_sum x h, mul_zero, sub_zero]

theorem upper_sum {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (t : ℝ) :
    (∑ j, upper x h t j) = ∑ j, x j := by
  unfold upper
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    direction_sum x h, correction_sum x h, mul_zero, sub_zero, add_zero]

theorem inactive_endpoints {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (hX : ∀ j, 0 ≤ x j) (t : ℝ) (j : Fin n) (hj : j ∉ active x) :
    lower x h t j = t ^ 2 ∧ upper x h t j = 3 * t ^ 2 := by
  simp [lower, upper, direction_inactive x h j hj, correction, hj, inactive_zero x hX j hj]

theorem positive_endpoints {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (hn : 2 ≤ n) (hX : ∀ j, 0 ≤ x j) (t : ℝ) (ht : 0 < t) (htr : t ≤ radius x h) (j : Fin n) :
    0 < lower x h t j ∧ 0 < upper x h t j := by
  by_cases hj : j ∈ active x
  · have hs := small_bounds x h t ht htr
    have hd := direction_bounds x h hn j
    have hC := compensation_le x h
    have hC0 := compensation_nonnegative x
    have hMin := positiveMinimum_le x h j hj
    have hMinPos := positiveMinimum_positive x h
    have hPower : t ^ 2 ≤ t := by nlinarith [hs.1]
    have hMulD := mul_le_mul_of_nonneg_left hd.2 ht.le
    have hMulDLower := mul_le_mul_of_nonneg_left hd.1 ht.le
    have hMulC := mul_le_mul_of_nonneg_right hC (sq_nonneg t)
    have hPowerN := mul_le_mul_of_nonneg_left hPower (show (0 : ℝ) ≤ n by positivity)
    simp only [lower, upper, correction, hj, ite_true]
    constructor <;> nlinarith [hs.2.2]
  · rw [(inactive_endpoints x h hX t j hj).1, (inactive_endpoints x h hX t j hj).2]
    constructor <;> positivity

theorem distinct_endpoints {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (hn : 2 ≤ n) (hX : ∀ j, 0 ≤ x j) (t : ℝ) (ht : 0 < t) (htr : t ≤ radius x h) (j : Fin n) :
    lower x h t j ≠ upper x h t j := by
  by_cases hj : j ∈ active x
  · by_cases hChosen : j = chosen x h
    · subst j
      have hC0 := compensation_nonnegative x
      have hk : (1 : ℝ) ≤ count x := by exact_mod_cast count_positive x h
      by_cases hOne : count x = 1
      · have hc : (0 : ℝ) < compensation x := by
          unfold compensation
          rw [hOne]
          simp only [Nat.cast_one, div_one]
          exact_mod_cast (by omega : 0 < n - 1)
        simp only [lower, upper, correction, chosen_mem, ite_true, direction_chosen, hOne, Nat.cast_one, sub_self, mul_zero]
        intro he
        nlinarith [sq_pos_of_pos ht]
      · have hk2 : (2 : ℝ) ≤ count x := by exact_mod_cast (by have hp := count_positive x h; omega : 2 ≤ count x)
        simp only [lower, upper, correction, chosen_mem, ite_true, direction_chosen]
        intro he
        have hc := mul_nonneg hC0 (sq_nonneg t)
        nlinarith
    · have hs := small_bounds x h t ht htr
      have hC := compensation_le x h
      have hCT := mul_le_mul_of_nonneg_right hC ht.le
      have hSlope : 0 < t * (1 - compensation x * t) := by
        apply mul_pos ht
        nlinarith [hs.2.1]
      simp only [lower, upper, correction, hj, ite_true, direction_other x h j hj hChosen, mul_one]
      intro he
      nlinarith [hSlope]
  · have he := inactive_endpoints x h hX t j hj
    rw [he.1, he.2]
    intro hEqual
    nlinarith [sq_pos_of_pos ht]

theorem endpoint_fullBudgets {n : ℕ} (x : Allocation n) (budget : ℝ)
    (hBudget : 0 < budget) (hX : FullBudget budget x) (hn : 2 ≤ n)
    (t : ℝ) (ht : 0 < t) (htr : t ≤ radius x (active_nonempty x budget hBudget hX)) :
    FullBudget budget (lower x (active_nonempty x budget hBudget hX) t) ∧
      FullBudget budget (upper x (active_nonempty x budget hBudget hX) t) := by
  let h := active_nonempty x budget hBudget hX
  refine ⟨⟨fun j => (positive_endpoints x h hn hX.1 t ht htr j).1.le, ?_⟩,
    ⟨fun j => (positive_endpoints x h hn hX.1 t ht htr j).2.le, ?_⟩⟩
  · rw [lower_sum]; exact hX.2
  · rw [upper_sum]; exact hX.2

end Blotto.RichSmoothingGeometry
