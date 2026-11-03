import Blotto.WordMachineRestriction
import Blotto.WordMachineSerialLaw
import Blotto.ProbabilityWordHeight

/-! Word bounds propagate through every state-machine request. The complete
specification certificate covers all branches; residual comparisons keep the
same denominator and hence obey the pending-digit bounds separately proved. -/

namespace Blotto

namespace WordTransition

def WordsHeight {S α : Type*} : WordTransition S α → ℕ → Prop
  | .done _, _ => True
  | .ask a b _ _ _ _, s => a < 2 ^ s ∧ b < 2 ^ s

end WordTransition

namespace WordChoiceTree

def WordsHeight {α : Type*} : WordChoiceTree α → ℕ → Prop
  | .leaf _, _ => True
  | .fork a b _ _ upper lower, s => a < 2 ^ s ∧ b < 2 ^ s ∧ upper.WordsHeight s ∧ lower.WordsHeight s

end WordChoiceTree

namespace WordStateMachine

theorem specification_wordsHeight {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (w : ℕ)
    (hWords : ∀ s, I s → (m.step s).WordsHeight w)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (s : S) (hI : I s) : (m.specification s).WordsHeight w := by
  have hAll : ∀ n, ∀ s, m.rank s = n → I s → (m.specification s).WordsHeight w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he hI
      cases ht : m.step s with
      | done x =>
        rw [m.specification_of_done s x ht]
        trivial
      | ask a b hb hab upper lower =>
        have hp := m.progress s
        have hw := hWords s hI
        have hc := hClosed s hI
        rw [ht] at hp hw hc
        rw [m.specification_of_ask s a b hb hab upper lower ht]
        exact ⟨hw.1, hw.2, ih (m.rank upper) (by omega) upper rfl hc.1,
          ih (m.rank lower) (by omega) lower rfl hc.2⟩
  exact hAll (m.rank s) s rfl hI

end WordStateMachine
end Blotto
