import Blotto.GeneralPaperFieldThresholdAttainment

/-! The current manuscript states affordability with weak total cost and
strict slack whenever a choice is open, and permits arbitrary feasible
representatives. Both forms follow from the retained response theorem. -/
namespace Blotto.GeneralPaperResponseLemmaRestatement
open scoped BigOperators Classical
open GeneralPaperFieldThresholdChoices GeneralPaperFieldThresholdAffordability
open GeneralPaperFieldThresholdResponses GeneralPaperFieldThresholdAttainment
set_option autoImplicit false

def Condition {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ) : Prop :=
  (∑ j,threshold p j) ≤ budget ∧ ((∃ j,opened p j=true) → (∑ j,threshold p j) < budget)

theorem condition_iff {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ) : Affordable p budget ↔ Condition p budget := by
  constructor
  · rintro (h | ⟨he,hc⟩)
    · exact ⟨h.le,fun _ => h⟩
    · refine ⟨he.le,?_⟩
      rintro ⟨j,hj⟩
      rw [hc j] at hj
      cases hj
  · intro h
    rcases lt_or_eq_of_le h.1 with hs | hs
    · exact Or.inl hs
    · refine Or.inr ⟨hs,fun j => ?_⟩
      cases ho : opened p j with
      | false => rfl
      | true => exact (not_lt_of_ge hs.ge (h.2 ⟨j,ho⟩)).elim

theorem feasibility_iff {m : ℕ} {T : Thresholds m} (p : Pattern T) (budget : ℝ) :
    (∃ y : Allocation m,Feasible budget y ∧ Makes p y) ↔ Condition p budget :=
  (affordable_iff p budget).trans (condition_iff p budget)

theorem representatives_maximum {m : ℕ} (T : Thresholds m) (budget : ℝ) (hBudget : 0 < budget)
    (represent : ∀ p : Pattern T,Condition p budget → Allocation m)
    (hRepresent : ∀ p hp,Feasible budget (represent p hp) ∧ Makes p (represent p hp))
    (v : Values m) (law : Mixed m) (hLaw : OnThresholds T law) :
    ∃ (p : Pattern T) (hp : Condition p budget),Feasible budget (represent p hp) ∧
      security v budget law=purePayoff v (represent p hp) law ∧
      ∀ (q : Pattern T) (hq : Condition q budget),purePayoff v (represent q hq) law ≤ purePayoff v (represent p hp) law := by
  obtain ⟨p,hp,_,_,he,hmax⟩ := security_attained_choice T budget hBudget.le v law hLaw
  have exactPayoff : ∀ (q : Pattern T) (hq : Condition q budget),
      purePayoff v (represent q hq) law=purePayoff v (realize q budget) law := by
    intro q hq
    exact purePayoff_exact T law hLaw _ _
      (share_exact q _ _ (hRepresent q hq).2 (realize_affordable q budget ((condition_iff q budget).mpr hq)).2) v
  let hp' := (condition_iff p budget).mp hp
  refine ⟨p,hp',(hRepresent p hp').1,?_,?_⟩
  · rw [exactPayoff p hp']
    exact he
  · intro q hq
    rw [exactPayoff q hq,exactPayoff p hp']
    exact hmax q ((condition_iff q budget).mpr hq)

end Blotto.GeneralPaperResponseLemmaRestatement
