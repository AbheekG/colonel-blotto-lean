import Blotto.GeneralPaperGridMixtures

/-! Canonical at-most-budget response bounds and exact independent payoffs
of the grid counterexample, for every q >= 3. -/
namespace Blotto.GeneralPaperGridCanonicalResponses
open MeasureTheory
open scoped BigOperators
open GeneralPaperGridMixtures GeneralPaperGridScalarPayoffs
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem row_dominates {B : ℝ} {x : Allocation 2} (hx : Feasible B x) : ∀ j, x j ≤ row B (x 0) j := by
  have hSum : x 0 + x 1 ≤ B := by simpa only [Fin.sum_univ_two] using hx.2
  intro j
  fin_cases j
  · exact le_rfl
  · change x 1 ≤ B-x 0
    linarith

theorem pure_mono {x z : Allocation 2} (h : ∀ j, x j ≤ z j) (law : Mixed 2) :
    purePayoff values x law ≤ purePayoff values z law :=
  integral_mono (integrable_payoff_right values x law) (integrable_payoff_right values z law)
    (fun y => payoff_mono_bid values h y)

theorem rich_response (q : ℕ) (x : Allocation 2) (hx : Feasible (3*(q : ℝ)) x) :
    purePayoff values x (poorLaw q) ≤ 2/3 := by
  have h := pure_mono (row_dominates hx) (poorLaw q)
  rw [against_poor] at h
  exact h.trans (rich_bound _ _)

theorem poor_grid_response (q : ℕ) (hq : 3 ≤ q) (x : Allocation 2)
    (hx : Feasible (2*(q : ℝ)) x) (hGrid : OnGrid 1 x) : purePayoff values x (richLaw q) ≤ 1/3 := by
  obtain ⟨y, hy⟩ := hGrid 0
  simp only [one_mul] at hy
  have hCoordinate := PureBoundaryEquilibria.feasible_coordinate_le hx (0 : Fin 2)
  rw [hy] at hCoordinate
  have hyN : y ≤ 2*q := by exact_mod_cast hCoordinate
  have h := pure_mono (row_dominates hx) (richLaw q)
  rw [hy, against_rich q hq] at h
  exact h.trans (GeneralPaperGridIntegerResponses.poor_bound q y hq hyN)

theorem rich_bid_interior (q : ℕ) (hq : 3 ≤ q) (i : Fin 4) :
    0 < (richBid q i : ℝ) ∧ (richBid q i : ℝ) < 3*(q : ℝ) := by
  have h : 0 < richBid q i ∧ richBid q i < 3*q := by
    fin_cases i <;> norm_num [richBid] <;> omega
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem rich_expected (q : ℕ) (hq : 3 ≤ q) : expected values (richLaw q) (poorLaw q) = 2/3 := by
  rw [richLaw, expected_probabilityMixture_left]
  have hEach (i : Fin 4) : expected values
      (PureBoundaryEquilibria.pointLaw (row (3*(q : ℝ)) (richBid q i))) (poorLaw q) = 2/3 := by
    rw [RichMinimax.expected_pointLaw_left, against_poor]
    exact rich_interior _ _ (rich_bid_interior q hq i).1 (rich_bid_interior q hq i).2
  simp_rw [hEach]
  rw [← Finset.sum_mul, rich_total]
  norm_num

theorem poor_expected (q : ℕ) (hq : 3 ≤ q) : expected values (poorLaw q) (richLaw q) = 1/3 := by
  have hc := expected_constant_sum values (richLaw q) (poorLaw q)
  rw [rich_expected q hq] at hc
  linarith

theorem rich_supported (q : ℕ) (hq : 3 ≤ q) : Supported (3*(q : ℝ)) (richLaw q) :=
  (rich_support q hq).mono (fun _ hx => fullBudget_feasible hx.1)

theorem poor_supported (q : ℕ) : Supported (2*(q : ℝ)) (poorLaw q) :=
  (poor_support q).mono (fun _ hx => fullBudget_feasible hx.1)

theorem rich_regret_zero (q : ℕ) (hq : 3 ≤ q) : regret values (3*(q : ℝ)) (richLaw q) (poorLaw q) = 0 := by
  have hNonneg := regret_nonneg values (richLaw q) (poorLaw q) (rich_supported q hq)
  have hUpper := security_le values (show 0 ≤ 3*(q : ℝ) by positivity) (poorLaw q) (rich_response q)
  unfold regret at hNonneg ⊢
  rw [rich_expected q hq] at hNonneg ⊢
  linarith

theorem real_row_full (B t : ℝ) (h0 : 0 ≤ t) (hB : t ≤ B) : FullBudget B (row B t) := by
  constructor
  · intro j
    fin_cases j
    · exact h0
    · change 0 ≤ B-t
      linarith
  · simp [row, Fin.sum_univ_succ]

theorem poor_profitable (q : ℕ) (hq : 3 ≤ q) :
    Feasible (2*(q : ℝ)) (row (2*(q : ℝ)) ((q : ℝ)-1/2)) ∧
    purePayoff values (row (2*(q : ℝ)) ((q : ℝ)-1/2)) (richLaw q) = 5/12 := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨fullBudget_feasible (real_row_full _ _ (by linarith) (by linarith)), ?_⟩
  rw [against_rich q hq]
  exact poor_off_grid _ hqR

theorem poor_regret_lower (q : ℕ) (hq : 3 ≤ q) : 1/12 ≤ regret values (2*(q : ℝ)) (poorLaw q) (richLaw q) := by
  have hd := poor_profitable q hq
  have hs := purePayoff_le_security values hd.1 (richLaw q)
  rw [hd.2] at hs
  unfold regret
  rw [poor_expected q hq]
  linarith

def GridEquilibrium (step A B : ℝ) (μ ν : Mixed 2) : Prop :=
  (∀ᵐ x ∂(μ : Measure (Allocation 2)), Feasible A x ∧ OnGrid step x) ∧
  (∀ᵐ x ∂(ν : Measure (Allocation 2)), Feasible B x ∧ OnGrid step x) ∧
  (∀ x, Feasible A x → OnGrid step x → purePayoff values x ν ≤ expected values μ ν) ∧
  (∀ y, Feasible B y → OnGrid step y → purePayoff values y μ ≤ expected values ν μ)

theorem integer_equilibrium (q : ℕ) (hq : 3 ≤ q) :
    GridEquilibrium 1 (3*(q : ℝ)) (2*(q : ℝ)) (richLaw q) (poorLaw q) := by
  refine ⟨(rich_support q hq).mono (fun _ hx => ⟨fullBudget_feasible hx.1, hx.2⟩),
    (poor_support q).mono (fun _ hx => ⟨fullBudget_feasible hx.1, hx.2⟩), ?_, ?_⟩
  · intro x hx _
    rw [rich_expected q hq]
    exact rich_response q x hx
  · intro y hy hGrid
    rw [poor_expected q hq]
    exact poor_grid_response q hq y hy hGrid

end Blotto.GeneralPaperGridCanonicalResponses
