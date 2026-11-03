import Blotto.CachedWordReindex
import Blotto.CachedWordCallbackWork

/-! State renaming preserves arbitrary weighted callback work when callback
prices commute with the renaming, in addition to transition equality. -/

namespace Blotto.WordStateMachine

theorem cachedCallbackWork_reindex_values {S T α β : Type*} (m : WordStateMachine S α) (target : WordStateMachine T β)
    (f : S → T) (g : α → β) (hStep : ∀ s, target.step (f s) = ((m.step s).mapValue g).mapState f)
    (charge : S → ℕ) (targetCharge : T → ℕ) (hCharge : ∀ s, targetCharge (f s) = charge s)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    target.cachedCallbackWork targetCharge N bits (cursor.mapState f) pos hpos = m.cachedCallbackWork charge N bits cursor pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold cachedCallbackWork
    conv_rhs => unfold cachedCallbackWork
    rw [hStep, hCharge]
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      have ih := m.cachedCallbackWork_reindex_values target f g hStep charge targetCharge hCharge N bits (.ofWords a b hb hab upper lower) pos hpos
      simpa only [WordTransition.mapValue, WordTransition.mapState, CachedWordCursor.mapState_ofWords] using congrArg (fun w => charge s + w) ih
  | coin a b hb hab upper lower =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold cachedCallbackWork
    conv_rhs => unfold cachedCallbackWork
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact m.cachedCallbackWork_reindex_values target f g hStep charge targetCharge hCharge N bits (.state lower) pos hpos
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      exact m.cachedCallbackWork_reindex_values target f g hStep charge targetCharge hCharge N bits (.state upper) pos hpos
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact m.cachedCallbackWork_reindex_values target f g hStep charge targetCharge hCharge N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := m.cachedCallbackWork_reindex_values target f g hStep charge targetCharge hCharge N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        simpa only [CachedWordCursor.mapState, apply_ite] using ih
    · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem cachedCallbackWork_reindex {S T α : Type*} (m : WordStateMachine S α) (target : WordStateMachine T α)
    (f : S → T) (hStep : ∀ s, target.step (f s) = (m.step s).mapState f)
    (charge : S → ℕ) (targetCharge : T → ℕ) (hCharge : ∀ s, targetCharge (f s) = charge s)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    target.cachedCallbackWork targetCharge N bits (cursor.mapState f) pos hpos =
      m.cachedCallbackWork charge N bits cursor pos hpos := by
  apply m.cachedCallbackWork_reindex_values target f id _ charge targetCharge hCharge
  intro s
  rw [hStep]
  cases m.step s <;> rfl

end Blotto.WordStateMachine
