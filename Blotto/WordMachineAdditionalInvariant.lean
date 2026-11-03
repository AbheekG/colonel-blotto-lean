import Blotto.WordMachineRestriction

/-! Existing proof-restricted controllers preserve any additional closed
invariant on their erased underlying states. No transition is changed. -/

namespace Blotto.WordTransition

theorem restrict_additionalPostcondition {S α : Type*} (I J : S → Prop) (P Q : α → Prop)
    (transition : WordTransition S α) (hI : transition.Postcondition I P)
    (hJ : transition.Postcondition J Q) :
    (transition.restrict I P hI).Postcondition (fun s => J s.1) (fun x => Q x.1) := by
  cases transition <;> exact hJ

end Blotto.WordTransition
namespace Blotto.WordStateMachine

theorem restricted_additionalClosed {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (P : α → Prop) (hI : ∀ s, I s → (m.step s).Postcondition I P)
    (J : S → Prop) (hJ : ∀ s, J s → (m.step s).Postcondition J (fun _ => True)) :
    ∀ s, J s.1 → ((m.restricted I P hI).step s).Postcondition (fun q => J q.1) (fun _ => True) := by
  intro s hs
  exact WordTransition.restrict_additionalPostcondition I J P (fun _ => True)
    (m.step s.1) (hI s.1 s.2) (hJ s.1 hs)

end Blotto.WordStateMachine
