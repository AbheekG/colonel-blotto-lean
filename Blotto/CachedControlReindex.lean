import Blotto.CachedControlWork
import Blotto.CachedCallbackRestriction

/-! State/output renaming and proof-wrapper erasure preserve encoding and
coin-body work when tracking flags agree. Word widths are never clipped. -/

namespace Blotto.WordStateMachine

theorem cachedControlWork_reindex_values {S T α β : Type*} (m : WordStateMachine S α) (target : WordStateMachine T β)
    (f : S → T) (g : α → β) (hStep : ∀ s, target.step (f s) = ((m.step s).mapValue g).mapState f)
    (tracked : S → Bool) (targetTracked : T → Bool) (hTracked : ∀ s, targetTracked (f s) = tracked s)
    (encodingPrice coinPrice : ℕ → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    target.cachedControlWork targetTracked encodingPrice coinPrice N bits (cursor.mapState f) pos hpos = m.cachedControlWork tracked encodingPrice coinPrice N bits cursor pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold cachedControlWork
    conv_rhs => unfold cachedControlWork
    rw [hStep]
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      simp only [WordTransition.mapValue, WordTransition.mapState, trackedCoin, hTracked]
      apply congrArg (fun z => (if trackedCoin tracked upper lower then encodingPrice (binaryWordWidth b) else 0) + z)
      have ih := m.cachedControlWork_reindex_values target f g hStep tracked targetTracked hTracked encodingPrice coinPrice N bits (.ofWords a b hb hab upper lower) pos hpos
      simpa only [CachedWordCursor.mapState_ofWords] using ih
  | @coin w a b hb hab upper lower =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold cachedControlWork
    conv_rhs => unfold cachedControlWork
    simp only [trackedCoin, hTracked]
    apply congrArg (fun z => (if trackedCoin tracked upper lower then coinPrice w else 0) + z)
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact m.cachedControlWork_reindex_values target f g hStep tracked targetTracked hTracked encodingPrice coinPrice N bits (.state lower) pos hpos
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      exact m.cachedControlWork_reindex_values target f g hStep tracked targetTracked hTracked encodingPrice coinPrice N bits (.state upper) pos hpos
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact m.cachedControlWork_reindex_values target f g hStep tracked targetTracked hTracked encodingPrice coinPrice N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := m.cachedControlWork_reindex_values target f g hStep tracked targetTracked hTracked encodingPrice coinPrice N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        simpa only [CachedWordCursor.mapState, apply_ite] using ih
    · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  all_goals first
    | (have hp := m.progress s; rw [hs] at hp; simp only [CachedWordCursor.ofWords]; omega)
    | omega

theorem cachedControlWork_restricted {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (P : α → Prop) (hI : ∀ s, I s → (m.step s).Postcondition I P)
    (tracked : S → Bool) (encodingPrice coinPrice : ℕ → ℕ) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor {s // I s}) (pos : ℕ) (hpos : pos ≤ N) :
    (m.restricted I P hI).cachedControlWork (fun s => tracked s.1) encodingPrice coinPrice N bits cursor pos hpos =
      m.cachedControlWork tracked encodingPrice coinPrice N bits (cursor.mapState Subtype.val) pos hpos := by
  symm
  apply (m.restricted I P hI).cachedControlWork_reindex_values m Subtype.val Subtype.val
    _ (fun s => tracked s.1) tracked (fun _ => rfl) encodingPrice coinPrice
  intro s
  exact (WordTransition.restrict_erase I P (m.step s.1) (hI s.1 s.2)).symm

end Blotto.WordStateMachine
