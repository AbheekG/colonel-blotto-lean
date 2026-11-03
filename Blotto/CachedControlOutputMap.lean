import Blotto.CachedControlReindex

/-! Output mapping preserves indexed Boolean encoding/body work. The mapped
emission itself is a distinct price, not hidden in this control observer. -/

namespace Blotto.WordStateMachine

theorem cachedControlWork_mapped {S α β : Type*} (m : WordStateMachine S α) (f : α → β)
    (tracked : S → Bool) (encodingPrice coinPrice : ℕ → ℕ) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    (m.mapped f).cachedControlWork tracked encodingPrice coinPrice N bits cursor pos hpos =
      m.cachedControlWork tracked encodingPrice coinPrice N bits cursor pos hpos := by
  have hStep : ∀ s, (m.mapped f).step s = ((m.step s).mapValue f).mapState id := by
    intro s
    rw [m.mapped_step]
    cases m.step s <;> rfl
  have he := m.cachedControlWork_reindex_values (m.mapped f) id f hStep tracked tracked (fun _ => rfl)
    encodingPrice coinPrice N bits cursor pos hpos
  have hi : cursor.mapState id = cursor := by cases cursor <;> rfl
  simpa only [hi] using he

end Blotto.WordStateMachine
