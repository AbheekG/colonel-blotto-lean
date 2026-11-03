import Blotto.RichSmoothingCDF
import Blotto.PureBoundaryEquilibria
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fixed-opponent approximation by actual regular full-budget rich laws.
Strictly unequal budgets exclude a tied bid at the rich player's sole
positive coordinate. Zero ties improve after smoothing. The limits retain
one whole-allocation draw and require no independent coordinate sampling. -/

namespace Blotto.RichSmoothingApproximation
open MeasureTheory Set Filter
open RichSmoothingGeometry RichSmoothingLaw RichSmoothingCDF
open scoped Topology BigOperators Classical

theorem active_singleton {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (hOne : count x = 1) : active x = {chosen x h} := by
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hOne
  have he : chosen x h = j := by simpa [hj] using chosen_mem x h
  simpa [he] using hj

theorem chosen_at_budget {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    {budget : ℝ} (hX : FullBudget budget x) (hOne : count x = 1) :
    x (chosen x h) = budget := by
  have hOther : ∀ j, j ≠ chosen x h → x j = 0 := by
    intro j hj
    apply inactive_zero x hX.1
    rw [active_singleton x h hOne]
    simpa using hj
  have hSum : (∑ j, x j) = x (chosen x h) := by
    apply Finset.sum_eq_single (chosen x h)
    · intro j _ hj; exact hOther j hj
    · simp
  exact hSum.symm.trans hX.2

theorem direction_ne_zero_at_tie {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    {A B : ℝ} (hX : FullBudget A x) (hBudgets : B < A) (y : Allocation n)
    (hY : Feasible B y) (j : Fin n) (hPositive : 0 < x j) (hTie : y j = x j) :
    direction x h j ≠ 0 := by
  have hj : j ∈ active x := (mem_active x j).mpr hPositive
  by_cases hChosen : j = chosen x h
  · subst j
    rw [direction_chosen]
    intro he
    have hOne : count x = 1 := by
      have hCast : (count x : ℝ) = 1 := by linarith
      exact_mod_cast hCast
    have hBudget := chosen_at_budget x h hX hOne
    have hUpper := PureBoundaryEquilibria.feasible_coordinate_le hY (chosen x h)
    rw [hTie,hBudget] at hUpper
    linarith
  · rw [direction_other x h j hj hChosen]
    norm_num

noncomputable def limitShare (x z : ℝ) : ℝ :=
  if z = 0 ∧ x = 0 then 0 else share z x

theorem limitShare_nonnegative (x z : ℝ) : 0 ≤ limitShare x z := by
  unfold limitShare
  split_ifs
  · exact le_rfl
  · exact share_nonneg _ _

theorem limitShare_le_share (x z : ℝ) : limitShare x z ≤ share z x := by
  unfold limitShare
  split_ifs
  · exact share_nonneg _ _
  · exact le_rfl

theorem limitShare_measurable (x : ℝ) : Measurable (limitShare x) := by
  have hSet : MeasurableSet {z : ℝ | z = 0 ∧ x = 0} := by
    by_cases hx : x = 0 <;> simp [hx]
  exact Measurable.ite hSet measurable_const
    (measurable_share.comp (measurable_id.prodMk measurable_const))

theorem coordinate_cdf_limit {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    {A B : ℝ} (hX : FullBudget A x) (hn : 2 ≤ n) (hBudgets : B < A)
    (y : Allocation n) (hY : Feasible B y) (j : Fin n) :
    Tendsto (fun k => closedCDF (law x h (step x h k)) j (y j))
      atTop (𝓝 (limitShare (x j) (y j))) := by
  rcases lt_trichotomy (y j) (x j) with hBelow | hTie | hAbove
  · have hLimit := below_cdf_limit x h hn hX.1 j (y j) hBelow
    have hZero : ¬(y j = 0 ∧ x j = 0) := by rintro ⟨hy,hx⟩; rw [hy,hx] at hBelow; exact hBelow.false
    simpa [limitShare, hZero, share, not_lt_of_ge hBelow.le, ne_of_lt hBelow] using hLimit
  · by_cases hx : x j = 0
    · have hy : y j = 0 := hTie.trans hx
      have hEq : (fun k => closedCDF (law x h (step x h k)) j (y j)) = fun _ : ℕ => 0 := by
        funext k
        rw [hy]
        exact zero_cdf x h hn hX.1 j k
      rw [hEq]
      simp [limitShare,hy,hx]
    · have hPositive : 0 < x j := lt_of_le_of_ne (hX.1 j) (Ne.symm hx)
      have hDirection := direction_ne_zero_at_tie x h hX hBudgets y hY j hPositive hTie
      have hLimit := tie_cdf_limit x h j hDirection
      simpa [limitShare,hx,hTie,share_tie] using hLimit
  · have hLimit := above_cdf_limit x h hn hX.1 j (y j) hAbove
    have hZero : ¬(y j = 0 ∧ x j = 0) := by rintro ⟨hy,hx⟩; rw [hy,hx] at hAbove; exact hAbove.false
    simpa [limitShare,hZero,share,hAbove] using hLimit

noncomputable def limitPayoff {n : ℕ} (values : Values n) (x y : Allocation n) : ℝ :=
  ∑ j, values.weight j * limitShare (x j) (y j)

theorem limitPayoff_nonnegative {n : ℕ} (values : Values n) (x y : Allocation n) :
    0 ≤ limitPayoff values x y :=
  Finset.sum_nonneg fun j _ => mul_nonneg (values.positive j).le (limitShare_nonnegative _ _)

theorem limitPayoff_le_payoff {n : ℕ} (values : Values n) (x y : Allocation n) :
    limitPayoff values x y ≤ payoff values y x :=
  Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (limitShare_le_share _ _) (values.positive j).le

theorem limitPayoff_measurable {n : ℕ} (values : Values n) (x : Allocation n) :
    Measurable (limitPayoff values x) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul ((limitShare_measurable (x j)).comp (measurable_pi_apply j))

theorem purePayoff_limit {n : ℕ} (values : Values n) (x : Allocation n) {A B : ℝ}
    (hA : 0 < A) (hX : FullBudget A x) (hn : 2 ≤ n) (hBudgets : B < A)
    (y : Allocation n) (hY : Feasible B y) :
    let h := active_nonempty x A hA hX
    Tendsto (fun k => purePayoff values y (law x h (step x h k)))
      atTop (𝓝 (limitPayoff values x y)) := by
  let h := active_nonempty x A hA hX
  have hLimit : Tendsto
      (fun k => ∑ j, values.weight j * closedCDF (law x h (step x h k)) j (y j))
      atTop (𝓝 (limitPayoff values x y)) := by
    apply tendsto_finsetSum
    intro j _
    exact (coordinate_cdf_limit x h hX hn hBudgets y hY j).const_mul _
  apply hLimit.congr
  intro k
  have hRegular := law_regular x A hA hX hn _ (step_positive x h k) (step_le_radius x h k)
  rw [purePayoff_marginals]
  apply Finset.sum_congr rfl
  intro j _
  rw [regular_strict_eq_closed hRegular]
  ring

theorem expected_limit {n : ℕ} (values : Values n) (x : Allocation n) {A B : ℝ}
    (hA : 0 < A) (hX : FullBudget A x) (hn : 2 ≤ n) (hBudgets : B < A)
    (opponent : Mixed n) (hOpponent : Supported B opponent) :
    let h := active_nonempty x A hA hX
    Tendsto (fun k => expected values opponent (law x h (step x h k)))
      atTop (𝓝 (∫ y, limitPayoff values x y ∂(opponent : Measure (Allocation n)))) := by
  let h := active_nonempty x A hA hX
  simp only [expected_iterated]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro k
    exact (integrable_purePayoff values opponent (law x h (step x h k))).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (purePayoff_nonneg values y _)]
      exact purePayoff_le_one values y _
  · exact hOpponent.mono fun y hy => purePayoff_limit values x hA hX hn hBudgets y hy

theorem limit_integral_le {n : ℕ} (values : Values n) (x : Allocation n) (opponent : Mixed n) :
    (∫ y, limitPayoff values x y ∂(opponent : Measure (Allocation n))) ≤
      1 - purePayoff values x opponent := by
  have hIntegrable : Integrable (limitPayoff values x) (opponent : Measure (Allocation n)) := by
    apply (integrable_const (1 : ℝ)).mono' (limitPayoff_measurable values x).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (limitPayoff_nonnegative values x y)]
      exact (limitPayoff_le_payoff values x y).trans (payoff_le_one values y x)
  have hOther : Integrable (fun y => payoff values y x) (opponent : Measure (Allocation n)) := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact ((measurable_payoff values).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs,abs_of_nonneg (payoff_nonneg values y x)]
        exact payoff_le_one values y x
  have hBound := integral_mono hIntegrable hOther (limitPayoff_le_payoff values x)
  have hSum : (∫ y, payoff values y x ∂(opponent : Measure (Allocation n))) +
      purePayoff values x opponent = 1 := by
    unfold purePayoff
    rw [← integral_add hOther (integrable_payoff_right values x opponent)]
    simp_rw [payoff_constant_sum]
    simp
  linarith

/-- For each fixed feasible opponent law and positive tolerance, an actual
regular rich whole law performs at least as well as the original pure bid
up to that tolerance. This is not uniform in the opponent law. -/
theorem exists_regular_approximation {n : ℕ} (values : Values n) (x : Allocation n) {A B : ℝ}
    (hA : 0 < A) (hX : FullBudget A x) (hn : 2 ≤ n) (hBudgets : B < A)
    (opponent : Mixed n) (hOpponent : Supported B opponent) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ smooth : Mixed n, Regular A smooth ∧
      purePayoff values x opponent - epsilon < expected values smooth opponent := by
  let h := active_nonempty x A hA hX
  let L := ∫ y, limitPayoff values x y ∂(opponent : Measure (Allocation n))
  have hLimit := expected_limit values x hA hX hn hBudgets opponent hOpponent
  have hEventual := hLimit.eventually_lt_const (show L < L + epsilon by linarith)
  obtain ⟨k,hk⟩ := hEventual.exists
  refine ⟨law x h (step x h k),
    law_regular x A hA hX hn _ (step_positive x h k) (step_le_radius x h k),?_⟩
  have hBound := limit_integral_le values x opponent
  have hSum := expected_constant_sum values (law x h (step x h k)) opponent
  change expected values opponent (law x h (step x h k)) < L + epsilon at hk
  change L ≤ 1 - purePayoff values x opponent at hBound
  linarith

/-- Regular rich responses have exactly the same upper bounds as all
canonical at-most pure responses against this fixed opponent law. -/
theorem regular_response_upper_bounds {n : ℕ} (values : Values n) {A B : ℝ}
    (hA : 0 < A) (hn : 2 ≤ n) (hBudgets : B < A)
    (opponent : Mixed n) (hOpponent : Supported B opponent) (C : ℝ) :
    (∀ smooth : Mixed n, Regular A smooth → expected values smooth opponent ≤ C) ↔
      security values A opponent ≤ C := by
  constructor
  · intro hBound
    apply full_spending_transfer values hA.le (⟨0,by omega⟩ : Fin n) opponent
    intro x hX
    by_contra hFail
    have he : 0 < purePayoff values x opponent - C := by linarith
    obtain ⟨smooth,hRegular,hBetter⟩ := exists_regular_approximation values x hA hX hn
      hBudgets opponent hOpponent (purePayoff values x opponent - C) he
    have hUpper := hBound smooth hRegular
    linarith
  · intro hBound smooth hRegular
    exact (expected_le_security values smooth opponent (regular_supported hRegular)).trans hBound

/-- The regular-response supremum approximates the actual continuous
security, including all at-most deviations, with no response oracle. -/
theorem exists_regular_near_security {n : ℕ} (values : Values n) {A B : ℝ}
    (hA : 0 < A) (hn : 2 ≤ n) (hBudgets : B < A)
    (opponent : Mixed n) (hOpponent : Supported B opponent) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ smooth : Mixed n, Regular A smooth ∧
      security values A opponent - epsilon < expected values smooth opponent := by
  by_contra hNo
  have hBound : ∀ smooth : Mixed n, Regular A smooth →
      expected values smooth opponent ≤ security values A opponent - epsilon := by
    intro smooth hRegular
    apply le_of_not_gt
    intro hBetter
    exact hNo ⟨smooth,hRegular,hBetter⟩
  have hSecurity := (regular_response_upper_bounds values hA hn hBudgets opponent hOpponent _).mp hBound
  linarith

end Blotto.RichSmoothingApproximation
