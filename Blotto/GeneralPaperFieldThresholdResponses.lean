import Blotto.GeneralPaperFieldThresholdAffordability
import Mathlib.Data.Fintype.Pi

/-! A finite feasible response set for arbitrary real threshold sets.
One selected response represents a deviation against every threshold row,
independently of battlefield values and joint row probabilities. -/
namespace Blotto.GeneralPaperFieldThresholdResponses
open scoped BigOperators Classical
open GeneralPaperFieldThresholdChoices GeneralPaperFieldThresholdAffordability
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable instance patternFintype {m : ℕ} (T : Thresholds m) : Fintype (Pattern T) := by
  unfold Pattern
  infer_instance

theorem share_exact {m : ℕ} {T : Thresholds m} (p : Pattern T) (y z : Allocation m)
    (hy : Makes p y) (hz : Makes p z) (j : Fin m) (t : ℝ) (ht : t ∈ T.field j) :
    share (y j) t = share (z j) t := by
  have hyl := makes_lower p y hy j
  have hzl := makes_lower p z hz j
  rcases lt_trichotomy t (threshold p j) with h | h | h
  · have hyt := h.trans_le hyl
    have hzt := h.trans_le hzl
    simp [share, hyt, hzt]
  · have hyj := hy j
    have hzj := hz j
    cases ho : opened p j with
    | false =>
      simp only [ho, Bool.false_eq_true, ite_false] at hyj hzj
      rw [hyj, hzj]
    | true =>
      simp only [ho, ite_true] at hyj hzj
      have hyt := h.trans_lt hyj.1
      have hzt := h.trans_lt hzj.1
      simp [share, hyt, hzt]
  · have hyt : y j < t := by
      have hj := hy j
      cases ho : opened p j with
      | false => simp only [ho, Bool.false_eq_true, ite_false] at hj; exact hj ▸ h
      | true => simp only [ho, ite_true] at hj; exact hj.2 t ht h
    have hzt : z j < t := by
      have hj := hz j
      cases ho : opened p j with
      | false => simp only [ho, Bool.false_eq_true, ite_false] at hj; exact hj ▸ h
      | true => simp only [ho, ite_true] at hj; exact hj.2 t ht h
    simp [share, not_lt_of_gt hyt, ne_of_lt hyt, not_lt_of_gt hzt, ne_of_lt hzt]

noncomputable def responses {m : ℕ} (T : Thresholds m) (budget : ℝ) : Finset (Allocation m) :=
  (Finset.univ.filter (fun p : Pattern T => Affordable p budget)).image (fun p => realize p budget)

theorem feasible {m : ℕ} (T : Thresholds m) (budget : ℝ) (z : Allocation m)
    (hz : z ∈ responses T budget) : Feasible budget z := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact (realize_affordable p budget (Finset.mem_filter.mp hp).2).1

theorem representation {m : ℕ} (T : Thresholds m) (budget : ℝ) (y : Allocation m)
    (hy : Feasible budget y) :
    ∃ z ∈ responses T budget, ∀ j t, t ∈ T.field j → share (y j) t = share (z j) t := by
  obtain ⟨p, hMakes⟩ := classification T y hy.1
  have hAffordable := affordable_of_makes p budget y hy hMakes
  have hz := realize_affordable p budget hAffordable
  exact ⟨realize p budget, Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hAffordable⟩, rfl⟩,
      fun j t ht => share_exact p y (realize p budget) hMakes hz.2 j t ht⟩

theorem every_row_payoff {m : ℕ} (T : Thresholds m) (budget : ℝ) (y : Allocation m)
    (hy : Feasible budget y) :
    ∃ z ∈ responses T budget, ∀ (weights : Fin m → ℝ) (row : Allocation m),
      (∀ j, row j ∈ T.field j) →
      (∑ j, weights j * share (y j) (row j)) = ∑ j, weights j * share (z j) (row j) := by
  obtain ⟨z, hz, hShares⟩ := representation T budget y hy
  exact ⟨z, hz, fun weights row hRow => Finset.sum_congr rfl
    (fun j _ => congrArg (fun t => weights j * t) (hShares j (row j) (hRow j)))⟩

end Blotto.GeneralPaperFieldThresholdResponses
