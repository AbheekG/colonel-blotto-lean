import Blotto.RealStateMachineRefinement

/-! Exact-real controller labels: one outer callback at every state visit
and one threshold comparison/uniform input at every nonterminal request.
Callback bodies and container ownership remain separate costs. -/

namespace Blotto.RealStateMachine
open scoped Classical

noncomputable def visits {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (seed : Fin C → ℝ)
    (s : S) (pos : ℕ) (_hpos : pos ≤ C) : ℕ :=
  match m.step s with
  | .done _ => 1
  | .ask p _ upper lower =>
    if hRead : pos < C then
      1 + m.visits C seed (if seed ⟨pos, hRead⟩ ≤ p then upper else lower) (pos + 1) (by omega)
    else 1
termination_by C - pos
decreasing_by omega

theorem visits_bound {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (seed : Fin C → ℝ)
    (s : S) (pos : ℕ) (hpos : pos ≤ C) : m.visits C seed s pos hpos ≤ m.rank s + 1 := by
  unfold visits
  cases hs : m.step s with
  | done x => dsimp only; omega
  | ask p hp upper lower =>
    have hProgress := m.progress s
    rw [hs] at hProgress
    dsimp only
    split
    · rename_i hRead
      split
      · have ih := m.visits_bound C seed upper (pos + 1) (by omega)
        omega
      · have ih := m.visits_bound C seed lower (pos + 1) (by omega)
        omega
    · omega
termination_by C - pos
decreasing_by all_goals omega

theorem calls_and_reads {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (s : S) (seed : Fin C → ℝ) :
    m.visits C seed s 0 (Nat.zero_le C) ≤ m.rank s + 1 ∧ (m.run C s seed).2 ≤ m.rank s :=
  ⟨m.visits_bound C seed s 0 (Nat.zero_le C), m.run_reads_rank C s seed⟩

end Blotto.RealStateMachine
