import Blotto.GeneralPaperFieldThresholdChoices

/-! Exact affordability of arbitrary field-dependent open/closed choices.
The realizing bump is derived from finite gaps and actual total slack. -/
namespace Blotto.GeneralPaperFieldThresholdAffordability
open scoped BigOperators Classical
open GeneralPaperFieldThresholdChoices
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem realize_strict {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ)
    (h : (∑ j, threshold p j) < budget) :
    Feasible budget (realize p budget) ∧ Makes p (realize p budget) := by
  have hp := bump_positive p budget h
  constructor
  · constructor
    · intro j
      have ht := T.nonnegative j (threshold p j) (p j).1.property
      dsimp only [realize]
      split_ifs <;> linarith
    · change (∑ j, (threshold p j + if opened p j then bump p budget else 0)) ≤ budget
      rw [Finset.sum_add_distrib]
      have hs : (∑ j : Fin m, if opened p j then bump p budget else 0) ≤ (m : ℝ) * bump p budget := by
        calc
          _ ≤ ∑ _j : Fin m, bump p budget := Finset.sum_le_sum (fun j _ => by split_ifs <;> linarith)
          _ = _ := by simp
      linarith [bump_budget p budget h]
  · intro j
    cases ho : opened p j with
    | false => simp [ho, realize]
    | true =>
      simp only [ho, ite_true, realize]
      refine ⟨by linarith, ?_⟩
      intro s hs hAbove
      have hg := gap_le T j (threshold p j) s (p j).1.property hs hAbove
      have hb : bump p budget ≤ gap T / 2 := min_le_left _ _
      have hgp := gap_positive T
      linarith

theorem realize_affordable {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ)
    (h : Affordable p budget) : Feasible budget (realize p budget) ∧ Makes p (realize p budget) := by
  rcases h with h | ⟨hSum, hClosed⟩
  · exact realize_strict p budget h
  · have he : realize p budget = threshold p := by funext j; simp [realize, hClosed j]
    rw [he]
    exact ⟨⟨fun j => T.nonnegative j _ (p j).1.property, hSum.le⟩,
      fun j => by simp [hClosed j]⟩

theorem affordable_of_makes {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ)
    (y : Allocation m) (hy : Feasible budget y) (hMakes : Makes p y) : Affordable p budget := by
  have hBelow := fun j => makes_lower p y hMakes j
  have hs : (∑ j, threshold p j) ≤ budget := (Finset.sum_le_sum (fun j _ => hBelow j)).trans hy.2
  rcases lt_or_eq_of_le hs with hs | hs
  · exact Or.inl hs
  · refine Or.inr ⟨hs, fun j => ?_⟩
    cases ho : opened p j with
    | false => rfl
    | true =>
      have hj := hMakes j
      simp only [ho, ite_true] at hj
      have hStrict := Finset.sum_lt_sum (fun i _ => hBelow i) ⟨j, Finset.mem_univ _, hj.1⟩
      exact (not_lt_of_ge hy.2 (hs ▸ hStrict)).elim

theorem affordable_iff {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ) :
    (∃ y : Allocation m, Feasible budget y ∧ Makes p y) ↔ Affordable p budget :=
  ⟨fun ⟨y, hy, hMakes⟩ => affordable_of_makes p budget y hy hMakes,
    fun h => ⟨realize p budget, realize_affordable p budget h⟩⟩

theorem classification {m : ℕ} (T : Thresholds m) (y : Allocation m) (hy : ∀ j, 0 ≤ y j) :
    ∃ p : Pattern T, Makes p y := by
  have hMax : ∀ j, ∃ t ∈ T.field j, t ≤ y j ∧ ∀ s ∈ T.field j, s ≤ y j → s ≤ t := by
    intro j
    let eligible := (T.field j).filter (fun t => t ≤ y j)
    have hz : 0 ∈ eligible := Finset.mem_filter.mpr ⟨T.zero j, hy j⟩
    obtain ⟨t, ht, hMax⟩ := Finset.exists_max_image eligible id ⟨0, hz⟩
    exact ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2,
      fun s hs hsy => hMax s (Finset.mem_filter.mpr ⟨hs, hsy⟩)⟩
  choose t ht hBelow hGreatest using hMax
  let p : Pattern T := fun j => (⟨t j, ht j⟩, decide (t j < y j))
  refine ⟨p, fun j => ?_⟩
  change (if decide (t j < y j) then _ else _)
  by_cases hStrict : t j < y j
  · simp only [hStrict, decide_true, ite_true]
    refine ⟨hStrict, fun s hs hAbove => ?_⟩
    exact lt_of_not_ge (fun hsy => (not_le_of_gt hAbove) (hGreatest j s hs hsy))
  · simp only [hStrict, decide_false, Bool.false_eq_true, ite_false]
    exact (le_antisymm (hBelow j) (le_of_not_gt hStrict)).symm

end Blotto.GeneralPaperFieldThresholdAffordability
