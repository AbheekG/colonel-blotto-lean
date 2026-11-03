import Blotto.CachedCallbackBounds

/-! A zero-priced initial callback leaves only the strict successor ranks.
This indexed bound applies under a closed reachable invariant without clipping
or changing the production price, reader position or packet. -/

namespace Blotto.WordStateMachine

theorem cachedCallbackWork_state_initial_bound {S α : Type*} (m : WordStateMachine S α)
    (charge : S → ℕ) (bound : ℕ) (hCharge : ∀ s, charge s ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (state : S) (hZero : charge state = 0) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork charge N bits (.state state) pos hpos ≤ bound * m.rank state := by
  conv_lhs => unfold cachedCallbackWork
  rw [hZero]
  cases hs : m.step state with
  | done value => exact Nat.zero_le _
  | ask a b hb hab upper lower =>
    simp only [Nat.zero_add]
    have hw := m.cachedCallbackWork_counts charge bound hCharge N bits (.ofWords a b hb hab upper lower) pos hpos
    rw [m.cachedCounts_refines, CachedWordCursor.reference_ofWords] at hw
    have hc := (m.indexedCounts_bounds N bits (.coin a b hb hab upper lower) pos hpos).1
    have hp := m.progress state
    rw [hs] at hp
    have hr : m.cursorCallbackBound (.coin a b hb hab upper lower) ≤ m.rank state := by
      simp only [cursorCallbackBound]
      omega
    exact hw.trans (Nat.mul_le_mul_left bound (hc.trans hr))

theorem cachedCallbackWork_state_initial_bound_under {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (charge : S → ℕ) (bound : ℕ) (hCharge : ∀ s, I s → charge s ≤ bound)
    (N : ℕ) (bits : Fin N → Bool) (state : S) (hI : I state) (hZero : charge state = 0)
    (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork charge N bits (.state state) pos hpos ≤ bound * m.rank state := by
  have hp := (m.restricted I (fun _ => True) hClosed).cachedCallbackWork_state_initial_bound
    (fun q => charge q.1) bound (fun q => hCharge q.1 q.2) N bits ⟨state, hI⟩ hZero pos hpos
  have he := m.cachedCallbackWork_restricted I (fun _ => True) hClosed charge N bits (.state ⟨state, hI⟩) pos hpos
  exact he.symm.le.trans hp

end Blotto.WordStateMachine
