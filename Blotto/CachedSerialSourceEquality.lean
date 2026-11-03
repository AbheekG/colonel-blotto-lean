import Blotto.CachedCallbackReindex
import Blotto.WordMachineSerialSourceWork

/-! A joined continuation cannot add source callback work, even when it
consumes the remaining cap or fails. Equality holds for arbitrary prices. -/

namespace Blotto.WordStateMachine

theorem cachedCallbackWork_zero {S α : Type*} (m : WordStateMachine S α)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork (fun _ => 0) N bits cursor pos hpos = 0 := by
  have h := m.cachedCallbackWork_counts (fun _ => 0) 0 (fun _ => le_rfl) N bits cursor pos hpos
  simpa only [Nat.zero_mul, Nat.le_zero] using h

theorem cachedCallbackWork_continuation_sourceZero {S α β : Type*} {T : α → Type*}
    (m : WordStateMachine S α) (next : ∀ a, WordStateMachine (T a) β)
    (start : ∀ a, T a) (C : ℕ) (hC : ∀ a, (next a).rank (start a) ≤ C)
    (charge : S → ℕ) (value : α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor (T value)) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialSourceCharge charge) N bits
      (cursor.mapState (.continuation value)) pos hpos = 0 := by
  rw [(next value).cachedCallbackWork_reindex (m.serial next start C hC)
    (.continuation value) (fun _ => rfl) (fun _ => 0) (serialSourceCharge charge) (fun _ => rfl)]
  exact (next value).cachedCallbackWork_zero N bits cursor pos hpos

theorem cachedCallbackWork_serialSource {S α β : Type*} {T : α → Type*}
    (m : WordStateMachine S α) (next : ∀ a, WordStateMachine (T a) β)
    (start : ∀ a, T a) (C : ℕ) (hC : ∀ a, (next a).rank (start a) ≤ C)
    (charge : S → ℕ) (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor S)
    (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialSourceCharge charge) N bits
      (cursor.mapState .source) pos hpos = m.cachedCallbackWork charge N bits cursor pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold cachedCallbackWork
    conv_rhs => unfold cachedCallbackWork
    simp only [serial, serialTransition, serialSourceCharge]
    cases hs : m.step s with
    | done value =>
      have hz := m.cachedCallbackWork_continuation_sourceZero next start C hC charge value N bits
        (.state (start value)) pos hpos
      conv_lhs at hz => rw [CachedWordCursor.mapState]; unfold cachedCallbackWork
      simp only [serial, serialTransition, serialSourceCharge, Nat.zero_add] at hz
      rw [hz]
    | ask a b hb hab upper lower =>
      have ih := m.cachedCallbackWork_serialSource next start C hC charge N bits
        (.ofWords a b hb hab upper lower) pos hpos
      simpa only [CachedWordCursor.mapState_ofWords, serial] using congrArg (fun w => charge s + w) ih
  | coin a b hb hab upper lower =>
    conv_lhs => rw [CachedWordCursor.mapState]; unfold cachedCallbackWork
    conv_rhs => unfold cachedCallbackWork
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      exact m.cachedCallbackWork_serialSource next start C hC charge N bits (.state lower) pos hpos
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      exact m.cachedCallbackWork_serialSource next start C hC charge N bits (.state upper) pos hpos
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        exact m.cachedCallbackWork_serialSource next start C hC charge N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
      · simp only [ite_eq_right hd]
        have ih := m.cachedCallbackWork_serialSource next start C hC charge N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        simpa only [CachedWordCursor.mapState, apply_ite] using ih
    · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  all_goals first
    | (have hp := m.progress s; rw [hs] at hp; simp only [CachedWordCursor.ofWords]; omega)
    | omega

theorem runCachedCallbackWork_serialSource {S α β : Type*} {T : α → Type*}
    (m : WordStateMachine S α) (next : ∀ a, WordStateMachine (T a) β)
    (start : ∀ a, T a) (C : ℕ) (hC : ∀ a, (next a).rank (start a) ≤ C)
    (charge : S → ℕ) (R : ℕ) (state : S) (bits : Fin R → Bool) :
    (m.serial next start C hC).runCachedCallbackWork (serialSourceCharge charge) R (.source state) bits =
      m.runCachedCallbackWork charge R state bits :=
  m.cachedCallbackWork_serialSource next start C hC charge R bits (.state state) 0 (Nat.zero_le R)

end Blotto.WordStateMachine
