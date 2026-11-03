import Blotto.WordMachineRestriction

/-! Native output mapping leaves controller states, word requests and rank
unchanged. Its specification is exactly the mapped original word tree. -/

namespace Blotto

namespace WordTransition

def mapValue {S α β : Type*} (f : α → β) : WordTransition S α → WordTransition S β
  | .done x => .done (f x)
  | .ask a b hb hab upper lower => .ask a b hb hab upper lower

theorem mapValue_progress {S α β : Type*} (f : α → β) (t : WordTransition S α) (rank : S → ℕ) (level : ℕ)
    (h : t.RankProgress rank level) : (t.mapValue f).RankProgress rank level := by
  cases t with
  | done x => trivial
  | ask a b hb hab upper lower => exact h

end WordTransition

namespace WordStateMachine

def mapped {S α β : Type*} (m : WordStateMachine S α) (f : α → β) : WordStateMachine S β where
  step := fun s => (m.step s).mapValue f
  rank := m.rank
  progress := fun s => WordTransition.mapValue_progress f (m.step s) m.rank (m.rank s) (m.progress s)

theorem mapped_step {S α β : Type*} (m : WordStateMachine S α) (f : α → β) (s : S) :
    (m.mapped f).step s = (m.step s).mapValue f := rfl

theorem mapped_specification {S α β : Type*} (m : WordStateMachine S α) (f : α → β) (s : S) :
    (m.mapped f).specification s = (m.specification s).map f := by
  have hAll : ∀ n, ∀ s : S, m.rank s = n → (m.mapped f).specification s = (m.specification s).map f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : m.step s with
      | done x =>
        have ht : (m.mapped f).step s = .done (f x) := by rw [m.mapped_step, hs]; rfl
        conv_lhs => unfold specification
        rw [ht]
        conv_rhs => unfold specification
        rw [hs]
        rfl
      | ask a b hb hab upper lower =>
        have hp := m.progress s
        rw [hs] at hp
        have ht : (m.mapped f).step s = .ask a b hb hab upper lower := by rw [m.mapped_step, hs]; rfl
        conv_lhs => unfold specification
        rw [ht]
        conv_rhs => unfold specification
        rw [hs]
        simp only [WordChoiceTree.map]
        rw [ih (m.rank upper) (by omega) upper rfl, ih (m.rank lower) (by omega) lower rfl]
  exact hAll (m.rank s) s rfl

theorem mapped_mean {S α β : Type*} (m : WordStateMachine S α) (f : α → β) (s : S) (g : β → ℝ) :
    ((m.mapped f).specification s).decode.mean g = (m.specification s).decode.mean (fun x => g (f x)) := by
  rw [m.mapped_specification, WordChoiceTree.map_mean]

end WordStateMachine
end Blotto
