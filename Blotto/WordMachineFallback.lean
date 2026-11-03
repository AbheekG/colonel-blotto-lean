import Blotto.WordMachineSerialLaw

/-! A deterministic feasible leaf can be prepared by following only lower
successors. It does not expand a specification tree and needs no random bits. -/

namespace Blotto

namespace WordChoiceTree

theorem bind_forLeaves {α β : Type*} (T : WordChoiceTree α) (f : α → WordChoiceTree β) (P : β → Prop)
    (h : ∀ x, (f x).decode.ForLeaves P) : (T.bind f).decode.ForLeaves P := by
  induction T with
  | leaf x => exact h x
  | fork a b hb hab upper lower hu hl => exact ⟨hu, hl⟩

end WordChoiceTree

namespace WordStateMachine

def chooseLeaf {S α : Type*} (m : WordStateMachine S α) (s : S) : α :=
  match _hs : m.step s with
  | .done value => value
  | .ask _ _ _ _ _ lower => m.chooseLeaf lower
termination_by m.rank s
decreasing_by
  have hp := m.progress s
  rw [_hs] at hp
  exact hp.2

theorem chooseLeaf_forLeaves {S α : Type*} (m : WordStateMachine S α) (s : S) (P : α → Prop)
    (h : (m.specification s).decode.ForLeaves P) : P (m.chooseLeaf s) := by
  have hAll : ∀ n, ∀ s : S, m.rank s = n → (m.specification s).decode.ForLeaves P → P (m.chooseLeaf s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he hs
      cases ht : m.step s with
      | done x =>
        rw [m.specification_of_done s x ht] at hs
        unfold chooseLeaf
        rw [ht]
        exact hs
      | ask a b hb hab upper lower =>
        have hp := m.progress s
        rw [ht] at hp
        rw [m.specification_of_ask s a b hb hab upper lower ht] at hs
        unfold chooseLeaf
        rw [ht]
        exact ih (m.rank lower) (by omega) lower rfl hs.2
  exact hAll (m.rank s) s rfl h

end WordStateMachine
end Blotto
