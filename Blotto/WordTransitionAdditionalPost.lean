import Blotto.WordMachineMap

/-! Erased proof restriction preserves extra state and output postconditions;
output mapping preserves closed state predicates. -/

namespace Blotto.WordTransition

theorem restrict_extraPostcondition {S α : Type*} (I J : S → Prop) (P Q : α → Prop)
    (t : WordTransition S α) (hBase : t.Postcondition I P) (hExtra : t.Postcondition J Q) :
    (t.restrict I P hBase).Postcondition (fun s => J s.1) (fun a => Q a.1) := by
  cases t <;> exact hExtra

theorem mapValue_statePostcondition {S α β : Type*} (f : α → β) (J : S → Prop)
    (t : WordTransition S α) (h : t.Postcondition J (fun _ => True)) :
    (t.mapValue f).Postcondition J (fun _ => True) := by
  cases t <;> exact h

end Blotto.WordTransition
