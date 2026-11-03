import Blotto.RealStateMachineRefinement
import Blotto.RealChoiceWordBridge

/-! Exact affine expectations follow terminating real-state transitions. -/

namespace Blotto.RealStateMachine

theorem specification_mean {S α : Type*} (m : RealStateMachine S α) (value : S → ℝ) (f : α → ℝ)
    (hValue : ∀ s, match m.step s with
      | .done x => f x = value s
      | .ask p _ upper lower => value s = p * value upper + (1 - p) * value lower) (s : S) :
    (m.specification s).mean f = value s := by
  have hAll : ∀ n, ∀ s, m.rank s = n → (m.specification s).mean f = value s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : m.step s with
      | done x =>
        have hv := hValue s
        rw [hs] at hv
        rw [m.specification_done s x hs]
        exact hv
      | ask p hp upper lower =>
        have hProgress := m.progress s
        have hv := hValue s
        rw [hs] at hProgress hv
        rw [m.specification_ask s p hp upper lower hs]
        change p * (m.specification upper).mean f + (1 - p) * (m.specification lower).mean f = value s
        rw [ih (m.rank upper) (by omega) upper rfl, ih (m.rank lower) (by omega) lower rfl]
        exact hv.symm
  exact hAll (m.rank s) s rfl

end Blotto.RealStateMachine
