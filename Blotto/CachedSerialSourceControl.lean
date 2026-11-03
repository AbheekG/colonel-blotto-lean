import Blotto.CachedControlUntracked
import Blotto.WordMachineSerialTrackedWords

/-! Source coin/encoding work stops at source completion; a joined terminal
continuation contributes zero source control work even when it exhausts the cap.
Tracking does not alter any word or decision in the full serial controller. -/

namespace Blotto.WordStateMachine

theorem cachedControlWork_continuation_sourceZero {S α β : Type*} {T : α → Type*}
    (m : WordStateMachine S α) (next : ∀ a, WordStateMachine (T a) β)
    (start : ∀ a, T a) (C : ℕ) (hC : ∀ a, (next a).rank (start a) ≤ C)
    (encodingPrice coinPrice : ℕ → ℕ) (value : α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor (T value)) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedControlWork serialSourceTag encodingPrice coinPrice N bits
      (cursor.mapState (fun s => (SerialState.continuation value s : SerialState S α T))) pos hpos = 0 := by
  have hStep : ∀ s, (m.serial next start C hC).step (.continuation value s) =
      (((next value).step s).mapValue id).mapState (fun s => (SerialState.continuation value s : SerialState S α T)) := by
    intro s
    change ((next value).step s).mapState (fun s => (SerialState.continuation value s : SerialState S α T)) = _
    cases (next value).step s <;> rfl
  rw [(next value).cachedControlWork_reindex_values (m.serial next start C hC)
    (.continuation value) id hStep (fun _ => false) serialSourceTag (fun _ => rfl) encodingPrice coinPrice]
  exact (next value).cachedControlWork_untracked (fun _ => false) (fun _ => rfl)
    encodingPrice coinPrice N bits cursor pos hpos

theorem cachedControlWork_serialSource {S α β : Type*} {T : α → Type*}
    (m : WordStateMachine S α) (next : ∀ a, WordStateMachine (T a) β)
    (start : ∀ a, T a) (C : ℕ) (hC : ∀ a, (next a).rank (start a) ≤ C)
    (encodingPrice coinPrice : ℕ → ℕ) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedControlWork serialSourceTag encodingPrice coinPrice N bits
      (cursor.mapState .source) pos hpos = m.cachedControlWork (fun _ => true) encodingPrice coinPrice N bits cursor pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold cachedControlWork
    conv_rhs => unfold cachedControlWork
    simp only [serial, serialTransition]
    cases hs : m.step s with
    | done value =>
      have hz := m.cachedControlWork_continuation_sourceZero next start C hC encodingPrice coinPrice value N bits
        (.state (start value)) pos hpos
      conv_lhs at hz => rw [CachedWordCursor.mapState]; unfold cachedControlWork
      simpa only [serial, serialTransition] using hz
    | ask a b hb hab upper lower =>
      simp only [trackedCoin, serialSourceTag, Bool.true_and, ite_true]
      apply congrArg (fun z => encodingPrice (binaryWordWidth b) + z)
      have ih := m.cachedControlWork_serialSource next start C hC encodingPrice coinPrice N bits
        (.ofWords a b hb hab upper lower) pos hpos
      simpa only [CachedWordCursor.mapState_ofWords, serial] using ih
  | @coin w a b hb hab upper lower =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold cachedControlWork
    conv_rhs => unfold cachedControlWork
    simp only [trackedCoin, serialSourceTag, Bool.true_and, ite_true]
    apply congrArg (fun z => coinPrice w + z)
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact m.cachedControlWork_serialSource next start C hC encodingPrice coinPrice N bits (.state lower) pos hpos
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      exact m.cachedControlWork_serialSource next start C hC encodingPrice coinPrice N bits (.state upper) pos hpos
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact m.cachedControlWork_serialSource next start C hC encodingPrice coinPrice N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := m.cachedControlWork_serialSource next start C hC encodingPrice coinPrice N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        simpa only [CachedWordCursor.mapState, apply_ite] using ih
    · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  all_goals first
    | (have hp := m.progress s; rw [hs] at hp; simp only [CachedWordCursor.ofWords]; omega)
    | omega

end Blotto.WordStateMachine
