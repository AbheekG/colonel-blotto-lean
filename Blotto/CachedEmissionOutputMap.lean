import Blotto.CachedEmissionWork
import Blotto.CachedCallbackReindex

/-! Output mapping transfers an explicit price by composition. This does not
make the output map free; its own emission price must be included separately. -/

namespace Blotto.WordStateMachine

theorem cachedEmissionWork_mapped {S α β : Type*} (m : WordStateMachine S α) (f : α → β)
    (price : β → ℕ) (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S)
    (pos : ℕ) (hpos : pos ≤ N) :
    (m.mapped f).cachedEmissionWork price N bits cursor pos hpos =
      m.cachedEmissionWork (fun x => price (f x)) N bits cursor pos hpos := by
  have hStep : ∀ s, (m.mapped f).step s = ((m.step s).mapValue f).mapState id := by
    intro s
    rw [m.mapped_step]
    cases m.step s <;> rfl
  have hCharge : ∀ s, (m.mapped f).emissionCharge price s = m.emissionCharge (fun x => price (f x)) s := by
    intro s
    unfold emissionCharge
    rw [m.mapped_step]
    cases m.step s <;> rfl
  have he := m.cachedCallbackWork_reindex_values (m.mapped f) id f hStep
    (m.emissionCharge (fun x => price (f x))) ((m.mapped f).emissionCharge price) hCharge
    N bits cursor pos hpos
  have hi : cursor.mapState id = cursor := by cases cursor <;> rfl
  simpa only [cachedEmissionWork, hi] using he

end Blotto.WordStateMachine
