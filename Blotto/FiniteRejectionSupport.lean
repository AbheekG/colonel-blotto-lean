import Blotto.FiniteImportanceExecution

/-! First-success and fallback outputs inherit a caller-supplied feasible set
on every attempt path. Zero-probability records are included in this invariant. -/

namespace Blotto
open scoped Classical

theorem firstAccepted_mem {α : Type*} {items : List (Option α)} {x : α}
    (h : firstAccepted items = some x) : some x ∈ items := by
  induction items with
  | nil => simp [firstAccepted] at h
  | cons item rest ih =>
    cases item with
    | none => exact List.mem_cons_of_mem _ (ih h)
    | some y =>
      have he : y = x := Option.some.inj h
      simp [he]

namespace FiniteRejectionAttempt

theorem run_invariant {r n : ℕ} (a : FiniteRejectionAttempt r n) (predicate : Fin n → Prop)
    (h : ∀ i x, a.result i = some x → predicate x) (k : ℕ)
    (path : Fin k → Fin r) (x : Fin n) (hx : a.run k path = some x) : predicate x := by
  have hm := firstAccepted_mem hx
  rcases List.mem_ofFn.mp hm with ⟨j, hj⟩
  exact h (path j) x hj

theorem fallback_invariant {r n : ℕ} (a : FiniteRejectionAttempt r n) (predicate : Fin n → Prop)
    (h : ∀ i x, a.result i = some x → predicate x) (fallback : Fin n) (hf : predicate fallback)
    (k : ℕ) (path : Fin k → Fin r) : predicate ((a.run k path).getD fallback) := by
  cases he : a.run k path with
  | none => exact hf
  | some x => exact a.run_invariant predicate h k path x he

end FiniteRejectionAttempt
namespace FiniteImportanceProposal

theorem attempt_invariant {r n : ℕ} (q : FiniteImportanceProposal r n) (predicate : Fin n → Prop)
    (hFeasible : ∀ p, predicate (q.output p)) (bound : ℝ) (hb : 0 < bound)
    (h : ∀ p, q.importance p ≤ bound) (i : Fin (r * 2)) (x : Fin n)
    (hx : (q.attempt bound hb h).result i = some x) : predicate x := by
  unfold attempt at hx
  dsimp only at hx
  split at hx
  · have he : q.output (finProdFinEquiv.symm i).1 = x := Option.some.inj hx
    exact he ▸ hFeasible _
  · cases hx

theorem run_feasible {r n : ℕ} (q : FiniteImportanceProposal r n) (predicate : Fin n → Prop)
    (hFeasible : ∀ p, predicate (q.output p)) (bound : ℝ) (hb : 0 < bound)
    (h : ∀ p, q.importance p ≤ bound) (fallback : Fin n) (hf : predicate fallback)
    (k : ℕ) (path : Fin k → Fin (r * 2)) :
    predicate (((q.attempt bound hb h).run k path).getD fallback) :=
  (q.attempt bound hb h).fallback_invariant predicate (q.attempt_invariant predicate hFeasible bound hb h)
    fallback hf k path

end FiniteImportanceProposal
end Blotto
