import Blotto.RealChoiceTreeLaw

/-! Real-RAM adaptive control uses one exact uniform comparison per request.
The runtime follows one state path through a fixed seed buffer; the real tree
is termination/distribution semantics and is not constructed by execution. -/

namespace Blotto
open scoped Classical

inductive RealTransition (S α : Type*) where
  | done (value : α)
  | ask (p : ℝ) (normalized : 0 ≤ p ∧ p ≤ 1) (upper lower : S)

structure RealStateMachine (S α : Type*) where
  step : S → RealTransition S α
  rank : S → ℕ
  progress : ∀ s, match step s with
    | .done _ => True
    | .ask _ _ upper lower => rank upper < rank s ∧ rank lower < rank s

namespace RealStateMachine

noncomputable def specification {S α : Type*} (m : RealStateMachine S α) (s : S) : RealChoiceTree α :=
  match _hs : m.step s with
  | .done x => .leaf x
  | .ask p hp upper lower => .fork p hp (m.specification upper) (m.specification lower)
termination_by m.rank s
decreasing_by
  all_goals have h := m.progress s
  all_goals rw [_hs] at h
  all_goals omega

noncomputable def runIndexed {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (seed : Fin C → ℝ)
    (s : S) (pos : ℕ) (_hpos : pos ≤ C) : Option α × ℕ :=
  match m.step s with
  | .done x => (some x, pos)
  | .ask p _ upper lower =>
    if hRead : pos < C then
      m.runIndexed C seed (if seed ⟨pos, hRead⟩ ≤ p then upper else lower) (pos + 1) (by omega)
    else (none, pos)
termination_by C - pos
decreasing_by omega

noncomputable def run {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (s : S) (seed : Fin C → ℝ) : Option α × ℕ :=
  m.runIndexed C seed s 0 (Nat.zero_le C)

noncomputable def output {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (s : S) (fallback : α)
    (seed : Fin C → ℝ) : α := (m.run C s seed).1.getD fallback

theorem specification_height {S α : Type*} (m : RealStateMachine S α) (s : S) : (m.specification s).height ≤ m.rank s := by
  have hAll : ∀ n, ∀ s, m.rank s = n → (m.specification s).height ≤ m.rank s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      unfold specification
      split
      · simp [RealChoiceTree.height]
      · rename_i p hp upper lower hs
        have h := m.progress s
        rw [hs] at h
        have hu := ih (m.rank upper) (by omega) upper rfl
        have hl := ih (m.rank lower) (by omega) lower rfl
        change 1 + max (m.specification upper).height (m.specification lower).height ≤ m.rank s
        omega
  exact hAll (m.rank s) s rfl

end RealStateMachine
end Blotto
