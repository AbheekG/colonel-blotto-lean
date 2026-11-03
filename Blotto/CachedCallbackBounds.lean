import Blotto.CachedCallbackRestriction

/-! Callback bounds apply at arbitrary indexed reader positions. Restricting
to a closed reachable invariant gives a bound for the original uncapped price;
no runtime invariant check, clipped price or new bit packet is introduced. -/

namespace Blotto.WordStateMachine

theorem cachedCallbackWork_state_bound {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (bound : ℕ) (hCharge : ∀ s, charge s ≤ bound) (N : ℕ) (bits : Fin N → Bool)
    (state : S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork charge N bits (.state state) pos hpos ≤ bound * (m.rank state + 1) := by
  have h := m.cachedCallbackWork_counts charge bound hCharge N bits (.state state) pos hpos
  rw [m.cachedCounts_refines] at h
  have hc := (m.indexedCounts_bounds N bits (.state state) pos hpos).1
  change (m.indexedCounts N bits (.state state) pos hpos).callbacks ≤ m.rank state + 1 at hc
  exact h.trans (Nat.mul_le_mul_left bound hc)

theorem cachedCallbackWork_state_bound_under {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (charge : S → ℕ) (bound : ℕ) (hCharge : ∀ s, I s → charge s ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (state : S) (hI : I state) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork charge N bits (.state state) pos hpos ≤ bound * (m.rank state + 1) := by
  have h := (m.restricted I (fun _ => True) hClosed).cachedCallbackWork_state_bound
    (fun q => charge q.1) bound (fun q => hCharge q.1 q.2) N bits ⟨state, hI⟩ pos hpos
  have he := m.cachedCallbackWork_restricted I (fun _ => True) hClosed charge N bits (.state ⟨state, hI⟩) pos hpos
  exact he.symm.le.trans h

theorem cachedCallbackWork_mapped {S α β : Type*} (m : WordStateMachine S α) (f : α → β)
    (charge : S → ℕ) (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    (m.mapped f).cachedCallbackWork charge N bits cursor pos hpos = m.cachedCallbackWork charge N bits cursor pos hpos := by
  have hStep : ∀ s, (m.mapped f).step s = ((m.step s).mapValue f).mapState id := by
    intro s
    rw [m.mapped_step]
    cases m.step s <;> rfl
  have he := m.cachedCallbackWork_reindex_values (m.mapped f) id f hStep charge charge (fun _ => rfl)
    N bits cursor pos hpos
  have hi : cursor.mapState id = cursor := by cases cursor <;> rfl
  simpa only [hi] using he

end Blotto.WordStateMachine
