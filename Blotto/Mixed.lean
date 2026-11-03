import Blotto.Model
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Arbitrary Borel laws on whole allocations, with independent players.
The feasible-support condition is almost sure; sampler pathwise guarantees
will be separate obligations. Security is a supremum, not a maximum. -/

namespace Blotto

open MeasureTheory Set
open scoped BigOperators

abbrev Mixed (n : ℕ) := ProbabilityMeasure (Allocation n)

def Supported {n : ℕ} (B : ℝ) (μ : Mixed n) : Prop :=
  ∀ᵐ x ∂(μ : Measure (Allocation n)), Feasible B x

theorem measurable_share : Measurable (fun z : ℝ × ℝ => share z.1 z.2) := by
  unfold share
  apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
    measurable_const measurable_const

theorem measurable_payoff {n : ℕ} (v : Values n) :
    Measurable (fun z : Allocation n × Allocation n => payoff v z.1 z.2) := by
  unfold payoff
  apply Finset.measurable_sum
  intro j _
  have hj1 : Measurable (fun z : Allocation n × Allocation n => z.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hj2 : Measurable (fun z : Allocation n × Allocation n => z.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact measurable_const.mul (measurable_share.comp (hj1.prodMk hj2))

theorem integrable_payoff {n : ℕ} (v : Values n)
    (ρ : Measure (Allocation n × Allocation n)) [IsFiniteMeasure ρ] :
    Integrable (fun z => payoff v z.1 z.2) ρ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_payoff v).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (payoff_nonneg v _ _)]
    exact payoff_le_one v _ _

noncomputable def purePayoff {n : ℕ} (v : Values n) (x : Allocation n)
    (ν : Mixed n) : ℝ := ∫ y, payoff v x y ∂(ν : Measure (Allocation n))

noncomputable def expected {n : ℕ} (v : Values n) (μ ν : Mixed n) : ℝ :=
  ∫ z, payoff v z.1 z.2 ∂((μ : Measure (Allocation n)).prod (ν : Measure (Allocation n)))

theorem integrable_purePayoff {n : ℕ} (v : Values n) (μ ν : Mixed n) :
    Integrable (fun x => purePayoff v x ν) (μ : Measure (Allocation n)) :=
  (integrable_payoff v _).integral_prod_left

theorem expected_iterated {n : ℕ} (v : Values n) (μ ν : Mixed n) :
    expected v μ ν = ∫ x, purePayoff v x ν ∂(μ : Measure (Allocation n)) :=
  integral_prod _ (integrable_payoff v _)

theorem integrable_payoff_right {n : ℕ} (v : Values n) (x : Allocation n)
    (ν : Mixed n) : Integrable (fun y => payoff v x y) (ν : Measure (Allocation n)) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((measurable_payoff v).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (payoff_nonneg v _ _)]
      exact payoff_le_one v _ _

theorem purePayoff_nonneg {n : ℕ} (v : Values n) (x : Allocation n) (ν : Mixed n) :
    0 ≤ purePayoff v x ν := integral_nonneg fun _ => payoff_nonneg v _ _

theorem purePayoff_le_one {n : ℕ} (v : Values n) (x : Allocation n) (ν : Mixed n) :
    purePayoff v x ν ≤ 1 := by
  simpa [purePayoff] using integral_mono (integrable_payoff_right v x ν)
    (integrable_const (1 : ℝ)) (fun y => payoff_le_one v x y)

theorem expected_constant_sum {n : ℕ} (v : Values n) (μ ν : Mixed n) :
    expected v μ ν + expected v ν μ = 1 := by
  have swap : expected v ν μ =
      ∫ z : Allocation n × Allocation n, payoff v z.2 z.1
        ∂((μ : Measure (Allocation n)).prod (ν : Measure (Allocation n))) := by
    exact (integral_prod_swap (μ := (μ : Measure (Allocation n)))
      (ν := (ν : Measure (Allocation n))) (fun z => payoff v z.2 z.1))
  have hi := integrable_payoff v
    ((μ : Measure (Allocation n)).prod (ν : Measure (Allocation n)))
  have hj : Integrable (fun z : Allocation n × Allocation n => payoff v z.2 z.1)
      ((μ : Measure (Allocation n)).prod (ν : Measure (Allocation n))) :=
    (integrable_payoff v
      ((ν : Measure (Allocation n)).prod (μ : Measure (Allocation n)))).swap
  rw [swap, expected, ← integral_add hi hj]
  simp_rw [payoff_constant_sum]
  simp

noncomputable def security {n : ℕ} (v : Values n) (B : ℝ) (ν : Mixed n) : ℝ :=
  sSup ((fun x => purePayoff v x ν) '' {x | Feasible B x})

theorem feasible_zero {n : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    Feasible B (fun _ : Fin n => 0) := by
  exact ⟨fun _ => le_rfl, by simpa using hB⟩

theorem security_set_nonempty {n : ℕ} (v : Values n) {B : ℝ} (hB : 0 ≤ B)
    (ν : Mixed n) : ((fun x => purePayoff v x ν) '' {x | Feasible B x}).Nonempty :=
  ⟨_, (fun _ => 0), feasible_zero hB, rfl⟩

theorem security_set_bddAbove {n : ℕ} (v : Values n) (B : ℝ) (ν : Mixed n) :
    BddAbove ((fun x => purePayoff v x ν) '' {x | Feasible B x}) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  exact purePayoff_le_one v x ν

theorem purePayoff_le_security {n : ℕ} (v : Values n) {B : ℝ} {x : Allocation n}
    (hx : Feasible B x) (ν : Mixed n) : purePayoff v x ν ≤ security v B ν :=
  le_csSup (security_set_bddAbove v B ν) ⟨x, hx, rfl⟩

theorem security_le {n : ℕ} (v : Values n) {B C : ℝ} (hB : 0 ≤ B) (ν : Mixed n)
    (h : ∀ x, Feasible B x → purePayoff v x ν ≤ C) : security v B ν ≤ C := by
  apply csSup_le (security_set_nonempty v hB ν)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem expected_le_security {n : ℕ} (v : Values n) {B : ℝ} (μ ν : Mixed n)
    (hμ : Supported B μ) : expected v μ ν ≤ security v B ν := by
  rw [expected_iterated]
  have h := integral_mono_ae (integrable_purePayoff v μ ν)
    (integrable_const (security v B ν))
    (hμ.mono fun x hx => purePayoff_le_security v hx ν)
  simpa using h

noncomputable def regret {n : ℕ} (v : Values n) (B : ℝ) (μ ν : Mixed n) : ℝ :=
  security v B ν - expected v μ ν

theorem regret_nonneg {n : ℕ} (v : Values n) {B : ℝ} (μ ν : Mixed n)
    (hμ : Supported B μ) : 0 ≤ regret v B μ ν :=
  sub_nonneg.mpr (expected_le_security v μ ν hμ)

/-- Manuscript (1.3): the actual independent-product regret identity. -/
theorem regret_sum {n : ℕ} (v : Values n) (A B : ℝ) (μ ν : Mixed n) :
    regret v A μ ν + regret v B ν μ = security v A ν + security v B μ - 1 := by
  have h := expected_constant_sum v μ ν
  unfold regret
  linarith

/-- A certified security sum controls each continuous regret. -/
theorem regrets_le_of_security_sum {n : ℕ} (v : Values n) {A B ε : ℝ}
    (μ ν : Mixed n) (hμ : Supported A μ) (hν : Supported B ν)
    (h : security v A ν + security v B μ ≤ 1 + ε) :
    regret v A μ ν ≤ ε ∧ regret v B ν μ ≤ ε := by
  have hsum := regret_sum v A B μ ν
  have hA := regret_nonneg v μ ν hμ
  have hB := regret_nonneg v ν μ hν
  constructor <;> linarith

/-- Full-budget pure deviation bounds imply bounds for the canonical domain. -/
theorem full_spending_transfer {n : ℕ} (v : Values n) {B C : ℝ} (hB : 0 ≤ B)
    (j : Fin n) (ν : Mixed n)
    (h : ∀ z, FullBudget B z → purePayoff v z ν ≤ C) : security v B ν ≤ C := by
  apply security_le v hB ν
  intro x hx
  apply le_trans _ (h _ (complete_full hx j))
  exact integral_mono (integrable_payoff_right v x ν)
    (integrable_payoff_right v (complete B x j) ν)
    (fun y => full_spending_dominates v hx j y)

end Blotto
