import Blotto.WordMachineSerialLaw

/-! A controller embedded in a larger state space retains its exact tree
semantics when every visited transition is the corresponding lifted step. -/

namespace Blotto.WordStateMachine

theorem embedding_specification {S T α : Type*} (a : WordStateMachine S α) (b : WordStateMachine T α)
    (embed : S → T) (h : ∀ s, b.step (embed s) = (a.step s).mapState embed) (s : S) :
    b.specification (embed s) = a.specification s := by
  have hAll : ∀ n, ∀ s : S, a.rank s = n → b.specification (embed s) = a.specification s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : a.step s with
      | done x =>
        have ht : b.step (embed s) = .done x := by rw [h s, hs]; rfl
        rw [b.specification_of_done _ _ ht, a.specification_of_done _ _ hs]
      | ask u d hd hud upper lower =>
        have hp := a.progress s
        rw [hs] at hp
        have ht : b.step (embed s) = .ask u d hd hud (embed upper) (embed lower) := by rw [h s, hs]; rfl
        rw [b.specification_of_ask _ _ _ _ _ _ _ ht, a.specification_of_ask _ _ _ _ _ _ _ hs]
        rw [ih (a.rank upper) (by omega) upper rfl, ih (a.rank lower) (by omega) lower rfl]
  exact hAll (a.rank s) s rfl

end Blotto.WordStateMachine
