import Blotto.CachedCallbackBounds

/-! Indexed callback potentials need price inequalities only on a closed
reachable invariant. Proof restriction preserves the original uncapped work.
No runtime test, clipping, counter reset or extra packet is introduced. -/

namespace Blotto.WordStateMachine

theorem cachedCallbackWork_state_potential_under {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (charge potential : S → ℕ)
    (hCost : ∀ s, I s → match m.step s with
      | .done _ => charge s ≤ potential s
      | .ask _ _ _ _ upper lower => charge s + potential upper ≤ potential s ∧ charge s + potential lower ≤ potential s)
    (N : ℕ) (bits : Fin N → Bool) (state : S) (hI : I state) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork charge N bits (.state state) pos hpos ≤ potential state := by
  let target := m.restricted I (fun _ => True) hClosed
  have hPotential : target.WorkPotential (fun q => charge q.1) (fun q => potential q.1) := by
    intro q
    have hc := hCost q.1 q.2
    have hp := hClosed q.1 q.2
    cases hs : m.step q.1 with
    | done value =>
      rw [hs] at hc hp
      have ht : target.step q = .done ⟨value, hp⟩ := by
        exact WordTransition.restrict_done I (fun _ => True) (m.step q.1) (hClosed q.1 q.2) value hs
      rw [ht]
      exact hc
    | ask a b hb hab upper lower =>
      rw [hs] at hc hp
      have ht : target.step q = .ask a b hb hab ⟨upper, hp.1⟩ ⟨lower, hp.2⟩ := by
        exact WordTransition.restrict_ask I (fun _ => True) (m.step q.1) (hClosed q.1 q.2) a b hb hab upper lower hs
      rw [ht]
      exact hc
  have h := target.indexedCallbackWork_potential (fun q => charge q.1) (fun q => potential q.1) hPotential
    N bits (.state ⟨state, hI⟩) pos hpos
  change target.indexedCallbackWork (fun q => charge q.1) N bits (.state ⟨state, hI⟩) pos hpos ≤ potential state at h
  have hCached := (target.cachedCallbackWork_refines (fun q => charge q.1) N bits
    (.state ⟨state, hI⟩) pos hpos).le.trans h
  have he := m.cachedCallbackWork_restricted I (fun _ => True) hClosed charge N bits (.state ⟨state, hI⟩) pos hpos
  exact he.symm.le.trans hCached

end Blotto.WordStateMachine
