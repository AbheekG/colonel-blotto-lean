import Blotto.GeneralPaperGridCanonicalResponses
import Mathlib.Analysis.SpecificLimits.Basic

/-! The fixed normalized game in prop:general:grid, including at-most-budget
grid deviations and nested discretizations converging to zero. -/
namespace Blotto.GeneralPaperGridCounterexample
open MeasureTheory Filter
open scoped Topology
open GeneralPaperGridMixtures GeneralPaperGridCanonicalResponses
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem measurable_grid (step : ℝ) : MeasurableSet {x : Allocation 2 | OnGrid step x} := by
  have he : {x : Allocation 2 | OnGrid step x} =
      ⋂ j : Fin 2, ⋃ z : ℕ, {x | x j = step * (z : ℝ)} := by
    ext x
    simp [OnGrid]
  rw [he]
  exact MeasurableSet.iInter fun j => MeasurableSet.iUnion fun z =>
    measurableSet_eq_fun (measurable_pi_apply j) measurable_const

theorem grid_scale (c : ℝ) {x : Allocation 2} (hx : OnGrid 1 x) :
    OnGrid c (scaleAllocation c x) := by
  intro j
  obtain ⟨z, hz⟩ := hx j
  refine ⟨z, ?_⟩
  simp only [one_mul] at hz
  simp only [scaleAllocation, hz]

theorem grid_inverse {c : ℝ} (hc : c ≠ 0) {x : Allocation 2} (hx : OnGrid c x) :
    OnGrid 1 (scaleAllocation c⁻¹ x) := by
  intro j
  obtain ⟨z, hz⟩ := hx j
  exact ⟨z, by simp [scaleAllocation, hz, hc]⟩

theorem grid_equilibrium_scale {c A B : ℝ} (hc : 0 < c) (μ ν : Mixed 2)
    (h : GridEquilibrium 1 A B μ ν) :
    GridEquilibrium c (c*A) (c*B) (scaleLaw c μ) (scaleLaw c ν) := by
  have hs (C : ℝ) (law : Mixed 2)
      (hl : ∀ᵐ x ∂(law : Measure (Allocation 2)), Feasible C x ∧ OnGrid 1 x) :
      ∀ᵐ x ∂(scaleLaw c law : Measure (Allocation 2)), Feasible (c*C) x ∧ OnGrid c x := by
    change ∀ᵐ x ∂Measure.map (scaleAllocation c) (law : Measure (Allocation 2)), _
    have hm : MeasurableSet {x : Allocation 2 | Feasible (c*C) x ∧ OnGrid c x} :=
      (measurable_feasible (c*C)).inter (measurable_grid c)
    rw [ae_map_iff (measurable_scaleAllocation c).aemeasurable hm]
    exact hl.mono (fun _ hx => ⟨scaleAllocation_feasible hc.le hx.1, grid_scale c hx.2⟩)
  have hr (C : ℝ) (own opponent : Mixed 2)
      (hResponse : ∀ x, Feasible C x → OnGrid 1 x →
        purePayoff values x opponent ≤ expected values own opponent)
      (x : Allocation 2) (hx : Feasible (c*C) x) (hg : OnGrid c x) :
      purePayoff values x (scaleLaw c opponent) ≤
        expected values (scaleLaw c own) (scaleLaw c opponent) := by
    let z := scaleAllocation c⁻¹ x
    have he : scaleAllocation c z = x := scaleAllocation_inverse_right hc.ne' x
    have hz : Feasible C z := (scaleAllocation_feasible_iff hc z).mp (by rw [he]; exact hx)
    have hzGrid : OnGrid 1 z := grid_inverse hc.ne' hg
    have hp := purePayoff_scale values hc z opponent
    rw [he] at hp
    rw [hp, expected_scale values hc]
    exact hResponse z hz hzGrid
  exact ⟨hs A μ h.1, hs B ν h.2.1, hr A μ ν h.2.2.1, hr B ν μ h.2.2.2⟩

noncomputable def delta (q : ℕ) : ℝ := 1/(3*(q : ℝ))
noncomputable def rich (q : ℕ) : Mixed 2 := scaleLaw (delta q) (richLaw q)
noncomputable def poor (q : ℕ) : Mixed 2 := scaleLaw (delta q) (poorLaw q)

theorem delta_positive (q : ℕ) (hq : 3 ≤ q) : 0 < delta q := by
  have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  unfold delta
  positivity

theorem budgets (q : ℕ) (hq : 3 ≤ q) :
    delta q * (3*(q : ℝ)) = 1 ∧ delta q * (2*(q : ℝ)) = 2/3 := by
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < q by omega))
  constructor <;> unfold delta <;> field_simp

theorem normalized_equilibrium (q : ℕ) (hq : 3 ≤ q) :
    GridEquilibrium (delta q) 1 (2/3) (rich q) (poor q) := by
  have h := grid_equilibrium_scale (delta_positive q hq) _ _ (integer_equilibrium q hq)
  rw [(budgets q hq).1, (budgets q hq).2] at h
  exact h

theorem normalized_rich_regret (q : ℕ) (hq : 3 ≤ q) :
    regret values 1 (rich q) (poor q) = 0 := by
  have h := regret_scale values (delta_positive q hq) (3*(q : ℝ)) (richLaw q) (poorLaw q)
  rw [(budgets q hq).1, rich_regret_zero q hq] at h
  exact h

theorem normalized_poor_regret (q : ℕ) (hq : 3 ≤ q) :
    1/12 ≤ regret values (2/3) (poor q) (rich q) := by
  have h := regret_scale values (delta_positive q hq) (2*(q : ℝ)) (poorLaw q) (richLaw q)
  rw [(budgets q hq).2] at h
  exact h ▸ poor_regret_lower q hq

theorem normalized_full_budgets (q : ℕ) (hq : 3 ≤ q) :
    (∀ᵐ x ∂(rich q : Measure (Allocation 2)), FullBudget 1 x) ∧
    (∀ᵐ x ∂(poor q : Measure (Allocation 2)), FullBudget (2/3) x) := by
  have ha := scaleLaw_fullBudget (delta_positive q hq).le (richLaw q)
    ((rich_support q hq).mono (fun _ hx => hx.1))
  have hb := scaleLaw_fullBudget (delta_positive q hq).le (poorLaw q)
    ((poor_support q).mono (fun _ hx => hx.1))
  rw [(budgets q hq).1] at ha
  rw [(budgets q hq).2] at hb
  exact ⟨ha, hb⟩

theorem paper_proposition (q : ℕ) (hq : 3 ≤ q) : ∃ μ ν : Mixed 2,
    GridEquilibrium (delta q) 1 (2/3) μ ν ∧
    regret values 1 μ ν = 0 ∧ 1/12 ≤ regret values (2/3) ν μ :=
  ⟨rich q, poor q, normalized_equilibrium q hq,
    normalized_rich_regret q hq, normalized_poor_regret q hq⟩

theorem dyadic_large (s : ℕ) (hs : 2 ≤ s) : 3 ≤ 2^s := by
  have h : (4 : ℕ) ≤ 2^s := by
    calc 4 = (2 : ℕ)^2 := by decide
         _ ≤ 2^s := pow_le_pow_right' (by decide) hs
  omega

theorem delta_dyadic (s : ℕ) : delta (2^s) = (1/3 : ℝ)*(1/2 : ℝ)^s := by
  simp only [delta, Nat.cast_pow, Nat.cast_ofNat, one_div, mul_inv_rev, inv_pow]
  ring

theorem grids_nested (s : ℕ) {x : Allocation 2} (hx : OnGrid (delta (2^s)) x) :
    OnGrid (delta (2^(s+1))) x := by
  intro j
  obtain ⟨z, hz⟩ := hx j
  refine ⟨2*z, ?_⟩
  rw [hz, delta_dyadic, delta_dyadic, pow_succ]
  push_cast
  ring

theorem meshes_tend_to_zero : Tendsto (fun s : ℕ => delta (2^s)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ) < 1 by norm_num)).const_mul (1/3 : ℝ)
  simpa only [mul_zero, ← delta_dyadic] using h

theorem nested_counterexamples (s : ℕ) (hs : 2 ≤ s) :
    GridEquilibrium (delta (2^s)) 1 (2/3) (rich (2^s)) (poor (2^s)) ∧
    regret values 1 (rich (2^s)) (poor (2^s)) = 0 ∧
    1/12 ≤ regret values (2/3) (poor (2^s)) (rich (2^s)) :=
  ⟨normalized_equilibrium _ (dyadic_large s hs),
    normalized_rich_regret _ (dyadic_large s hs), normalized_poor_regret _ (dyadic_large s hs)⟩

end Blotto.GeneralPaperGridCounterexample
