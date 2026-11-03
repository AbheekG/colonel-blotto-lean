import Blotto.GeneralPaperGridIntegerResponses

/-! The counterexample's actual independent whole-allocation laws in
integer budget units. The rich player has four atoms; the poor player three.
All support/grid and payoff claims use canonical mixed strategies. -/
namespace Blotto.GeneralPaperGridMixtures
open MeasureTheory
open scoped BigOperators
open GeneralPaperGridScalarPayoffs
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

noncomputable def values : Values 2 :=
  ⟨fun _ => 1/2, fun _ => by norm_num, by norm_num [Fin.sum_univ_succ]⟩

def row (B t : ℝ) : Allocation 2 := ![t, B-t]
def richBid (q : ℕ) : Fin 4 → ℕ := ![q-1, q+1, 2*q, 2*q+1]
def poorBid (q : ℕ) : Fin 3 → ℕ := ![0, q, 2*q]
noncomputable def richWeight : Fin 4 → ℝ := ![1/3, 1/6, 1/3, 1/6]
noncomputable def poorWeight : Fin 3 → ℝ := fun _ => 1/3

theorem rich_nonnegative (i : Fin 4) : 0 ≤ richWeight i := by fin_cases i <;> norm_num [richWeight]
theorem poor_nonnegative (i : Fin 3) : 0 ≤ poorWeight i := by norm_num [poorWeight]
theorem rich_total : ∑ i, richWeight i = 1 := by norm_num [richWeight, Fin.sum_univ_succ]
theorem poor_total : ∑ i, poorWeight i = 1 := by norm_num [poorWeight, Fin.sum_univ_succ]

noncomputable def richLaw (q : ℕ) : Mixed 2 := probabilityMixture richWeight
  (fun i => PureBoundaryEquilibria.pointLaw (row (3*(q : ℝ)) (richBid q i))) rich_nonnegative rich_total
noncomputable def poorLaw (q : ℕ) : Mixed 2 := probabilityMixture poorWeight
  (fun i => PureBoundaryEquilibria.pointLaw (row (2*(q : ℝ)) (poorBid q i))) poor_nonnegative poor_total

def OnGrid (step : ℝ) (x : Allocation 2) : Prop := ∀ j, ∃ z : ℕ, x j = step * (z : ℝ)

theorem row_payoff (B t C u : ℝ) : payoff values (row B t) (row C u) = pair B t C u := by
  norm_num [payoff, values, row, Fin.sum_univ_succ, pair]
  ring

theorem nat_row_full (B t : ℕ) (ht : t ≤ B) : FullBudget (B : ℝ) (row B t) := by
  constructor
  · intro j
    fin_cases j
    · exact Nat.cast_nonneg t
    · change 0 ≤ (B : ℝ) - (t : ℝ)
      exact sub_nonneg.mpr (by exact_mod_cast ht)
  · simp [row, Fin.sum_univ_succ]

theorem nat_row_grid (B t : ℕ) (ht : t ≤ B) : OnGrid 1 (row B t) := by
  intro j
  fin_cases j
  · exact ⟨t, by simp [row]⟩
  · refine ⟨B-t, ?_⟩
    simp [row, Nat.cast_sub ht]

theorem rich_bid_bound (q : ℕ) (hq : 3 ≤ q) (i : Fin 4) : richBid q i ≤ 3*q := by
  fin_cases i <;> norm_num [richBid] <;> omega

theorem poor_bid_bound (q : ℕ) (i : Fin 3) : poorBid q i ≤ 2*q := by
  fin_cases i
  · change 0 ≤ 2*q; omega
  · change q ≤ 2*q; omega
  · exact le_rfl

theorem rich_support (q : ℕ) (hq : 3 ≤ q) :
    ∀ᵐ x ∂(richLaw q : Measure (Allocation 2)), FullBudget (3*(q : ℝ)) x ∧ OnGrid 1 x := by
  apply probabilityMixture_ae
  intro i
  change ∀ᵐ x ∂Measure.dirac (row (3*(q : ℝ)) (richBid q i)), _
  rw [ae_dirac_eq]
  have hf := nat_row_full (3*q) (richBid q i) (rich_bid_bound q hq i)
  have hg := nat_row_grid (3*q) (richBid q i) (rich_bid_bound q hq i)
  change FullBudget _ (row _ _) ∧ OnGrid 1 (row _ _)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using And.intro hf hg

theorem poor_support (q : ℕ) :
    ∀ᵐ x ∂(poorLaw q : Measure (Allocation 2)), FullBudget (2*(q : ℝ)) x ∧ OnGrid 1 x := by
  apply probabilityMixture_ae
  intro i
  change ∀ᵐ x ∂Measure.dirac (row (2*(q : ℝ)) (poorBid q i)), _
  rw [ae_dirac_eq]
  have hf := nat_row_full (2*q) (poorBid q i) (poor_bid_bound q i)
  have hg := nat_row_grid (2*q) (poorBid q i) (poor_bid_bound q i)
  change FullBudget _ (row _ _) ∧ OnGrid 1 (row _ _)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using And.intro hf hg

theorem pure_finite {k : ℕ} (w : Fin k → ℝ) (rows : Fin k → Allocation 2)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (x : Allocation 2) :
    purePayoff values x (probabilityMixture w (fun i => PureBoundaryEquilibria.pointLaw (rows i)) hw hs) =
      ∑ i, w i * payoff values x (rows i) := by
  unfold purePayoff
  rw [probabilityMixture_integral w _ hw hs _ (fun i => integrable_payoff_right values x _)]
  change (∑ i, w i * purePayoff values x (PureBoundaryEquilibria.pointLaw (rows i))) = _
  simp_rw [PureBoundaryEquilibria.purePayoff_pointLaw]

theorem against_poor (q : ℕ) (t : ℝ) : purePayoff values (row (3*(q : ℝ)) t) (poorLaw q) = richMean q t := by
  rw [poorLaw, pure_finite]
  norm_num [poorWeight, poorBid, Fin.sum_univ_succ, row_payoff, richMean]
  ring

theorem against_rich (q : ℕ) (hq : 3 ≤ q) (y : ℝ) :
    purePayoff values (row (2*(q : ℝ)) y) (richLaw q) = poorMean q y := by
  have hq1 : 1 ≤ q := by omega
  rw [richLaw, pure_finite]
  norm_num [richWeight, richBid, Fin.sum_univ_succ, row_payoff, poorMean, Nat.cast_sub hq1]
  ring

end Blotto.GeneralPaperGridMixtures
