import Blotto.GeneralPaperFieldThresholdResponses

/-! The revised paper response lemma for arbitrary field-dependent finite
thresholds and arbitrary whole-allocation laws on them. The continuous
security supremum is an attained finite maximum, including all zero ties. -/
namespace Blotto.GeneralPaperFieldThresholdAttainment
open MeasureTheory
open scoped BigOperators Classical
open GeneralPaperFieldThresholdChoices GeneralPaperFieldThresholdAffordability
open GeneralPaperFieldThresholdResponses
set_option autoImplicit false
set_option maxHeartbeats 3500000

def OnThresholds {m : ℕ} (T : Thresholds m) (law : Mixed m) : Prop :=
  ∀ᵐ row ∂(law : Measure (Allocation m)), ∀ j, row j ∈ T.field j

theorem purePayoff_exact {m : ℕ} (T : Thresholds m) (law : Mixed m) (hLaw : OnThresholds T law)
    (y z : Allocation m)
    (hShares : ∀ j t, t ∈ T.field j → share (y j) t = share (z j) t) (v : Values m) :
    purePayoff v y law = purePayoff v z law := by
  unfold purePayoff
  apply integral_congr_ae
  exact hLaw.mono fun row hRow => by
    unfold payoff
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun t => v.weight j * t) (hShares j (row j) (hRow j)))

theorem simultaneous_law_representation {m : ℕ} (T : Thresholds m) (budget : ℝ)
    (y : Allocation m) (hy : Feasible budget y) :
    ∃ z ∈ responses T budget, ∀ (v : Values m) (law : Mixed m), OnThresholds T law →
      purePayoff v y law = purePayoff v z law := by
  obtain ⟨z, hz, hShares⟩ := representation T budget y hy
  exact ⟨z, hz, fun v law hLaw => purePayoff_exact T law hLaw y z hShares v⟩

theorem nonempty {m : ℕ} (T : Thresholds m) (budget : ℝ) (hBudget : 0 ≤ budget) :
    (responses T budget).Nonempty := by
  obtain ⟨z, hz, _⟩ := representation T budget (fun _ => 0) (feasible_zero hBudget)
  exact ⟨z, hz⟩

theorem security_attained {m : ℕ} (T : Thresholds m) (budget : ℝ) (hBudget : 0 ≤ budget)
    (v : Values m) (law : Mixed m) (hLaw : OnThresholds T law) :
    ∃ best ∈ responses T budget, Feasible budget best ∧
      security v budget law = purePayoff v best law ∧
      ∀ z ∈ responses T budget, purePayoff v z law ≤ purePayoff v best law := by
  obtain ⟨best, hBest, hMax⟩ := Finset.exists_max_image (responses T budget)
    (fun z => purePayoff v z law) (nonempty T budget hBudget)
  refine ⟨best, hBest, feasible T budget best hBest, le_antisymm ?_
    (purePayoff_le_security v (feasible T budget best hBest) law), hMax⟩
  apply security_le v hBudget law
  intro y hy
  obtain ⟨z, hz, hExact⟩ := simultaneous_law_representation T budget y hy
  rw [hExact v law hLaw]
  exact hMax z hz

theorem security_attained_choice {m : ℕ} (T : Thresholds m) (budget : ℝ) (hBudget : 0 ≤ budget)
    (v : Values m) (law : Mixed m) (hLaw : OnThresholds T law) :
    ∃ p : Pattern T, Affordable p budget ∧ Makes p (realize p budget) ∧
      Feasible budget (realize p budget) ∧
      security v budget law = purePayoff v (realize p budget) law ∧
      ∀ q : Pattern T, Affordable q budget →
        purePayoff v (realize q budget) law ≤ purePayoff v (realize p budget) law := by
  obtain ⟨best, hBest, hFeasible, hExact, hMax⟩ := security_attained T budget hBudget v law hLaw
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hBest
  have hAffordable := (Finset.mem_filter.mp hp).2
  exact ⟨p, hAffordable, (realize_affordable p budget hAffordable).2, hFeasible, hExact,
    fun q hq => hMax _ (Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩)⟩

theorem paper_response_lemma {m : ℕ} (T : Thresholds m) (budget : ℝ) (hBudget : 0 < budget) :
    (∀ p : Pattern T, (∃ y : Allocation m, Feasible budget y ∧ Makes p y) ↔
      (∑ j, threshold p j) < budget ∨
        (∑ j, threshold p j) = budget ∧ ∀ j, opened p j = false) ∧
    ∃ Y : Finset (Allocation m),
      (∀ z ∈ Y, Feasible budget z) ∧
      (∀ y : Allocation m, Feasible budget y →
        ∃ z ∈ Y, ∀ (weights : Fin m → ℝ) (row : Allocation m),
          (∀ j, row j ∈ T.field j) →
          (∑ j, weights j * share (y j) (row j)) = ∑ j, weights j * share (z j) (row j)) ∧
      ∀ (v : Values m) (law : Mixed m), OnThresholds T law →
        ∃ best ∈ Y, security v budget law = purePayoff v best law ∧
          ∀ z ∈ Y, purePayoff v z law ≤ purePayoff v best law := by
  refine ⟨fun p => affordable_iff p budget, responses T budget,
    fun z hz => feasible T budget z hz, fun y hy => every_row_payoff T budget y hy, ?_⟩
  intro v law hLaw
  obtain ⟨best, hBest, _, hExact, hMax⟩ := security_attained T budget hBudget.le v law hLaw
  exact ⟨best, hBest, hExact, hMax⟩

end Blotto.GeneralPaperFieldThresholdAttainment
