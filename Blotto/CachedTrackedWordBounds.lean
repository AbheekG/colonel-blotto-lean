import Blotto.CachedWordControllerHeight

/-! Cached width certificates may track only selected coin phases. Untracked
requests retain their true words and control flow without a width restriction.
All state invariants still propagate on every reached packet/cap path. -/

namespace Blotto

def trackedCoin {S : Type*} (tracked : S → Bool) (upper lower : S) : Bool := tracked upper && tracked lower

namespace WordTransition

def TrackedWordsHeight {S α : Type*} (tracked : S → Bool) : WordTransition S α → ℕ → Prop
  | .done _, _ => True
  | .ask a b _ _ upper lower, limit => trackedCoin tracked upper lower = true → a < 2 ^ limit ∧ b < 2 ^ limit

end WordTransition
end Blotto

namespace Blotto.CachedWordCursor

def TrackedBounded {S : Type*} (I : S → Prop) (tracked : S → Bool) (limit : ℕ) : CachedWordCursor S → Prop
  | .state s => I s
  | @CachedWordCursor.coin _ w _ _ _ _ upper lower => (trackedCoin tracked upper lower = true → w ≤ limit) ∧ I upper ∧ I lower

theorem ofWords_trackedBounded {S : Type*} (I : S → Prop) (tracked : S → Bool) (limit a b : ℕ) (hb : 0 < b)
    (hab : a ≤ b) (upper lower : S) (hB : trackedCoin tracked upper lower = true → b < 2 ^ limit)
    (hUpper : I upper) (hLower : I lower) :
    (ofWords a b hb hab upper lower).TrackedBounded I tracked limit := by
  change (trackedCoin tracked upper lower = true → binaryWordWidth b ≤ limit) ∧ I upper ∧ I lower
  refine ⟨?_, hUpper, hLower⟩
  intro hTracked
  have hLog := (Nat.log2_lt (ne_of_gt hb)).mpr (hB hTracked)
  unfold binaryWordWidth
  omega

end Blotto.CachedWordCursor
namespace Blotto.WordStateMachine

def CachedTrackedWordsBounded {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (tracked : S → Bool) (limit N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : Prop :=
  match cursor with
  | .state s => I s ∧ match _hs : m.step s with
    | .done _ => True
    | .ask a b hb hab upper lower =>
      m.CachedTrackedWordsBounded I tracked limit N bits (.ofWords a b hb hab upper lower) pos hpos
  | @CachedWordCursor.coin _ w a b hb hab upper lower =>
    (trackedCoin tracked upper lower = true → w ≤ limit) ∧ if hz : a.isZero = true then m.CachedTrackedWordsBounded I tracked limit N bits (.state lower) pos hpos else
      if he : a.same b = true then m.CachedTrackedWordsBounded I tracked limit N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.CachedTrackedWordsBounded I tracked limit N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.CachedTrackedWordsBounded I tracked limit N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
            (pos + 1) (by omega)
        else True
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem runCachedIndexed_trackedWordsBounded {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (tracked : S → Bool) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).TrackedWordsHeight tracked limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True)) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) (hCursor : cursor.TrackedBounded I tracked limit) :
    m.CachedTrackedWordsBounded I tracked limit N bits cursor pos hpos := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at hCursor
    unfold CachedTrackedWordsBounded
    refine ⟨hCursor, ?_⟩
    cases hs : m.step s with
    | done value => trivial
    | ask a b hb hab upper lower =>
      have hw := hWords s hCursor
      have hc := hClosed s hCursor
      rw [hs] at hw hc
      exact m.runCachedIndexed_trackedWordsBounded I tracked limit hWords hClosed N bits
        (.ofWords a b hb hab upper lower) pos hpos
        (CachedWordCursor.ofWords_trackedBounded I tracked limit a b hb hab upper lower (fun ht => (hw ht).2) hc.1 hc.2)
  | @coin w a b hb hab upper lower =>
    rw [hCursorEq] at hCursor
    unfold CachedTrackedWordsBounded
    refine ⟨hCursor.1, ?_⟩
    by_cases hz : a.isZero = true
    · rw [dite_eq_left hz]
      exact m.runCachedIndexed_trackedWordsBounded I tracked limit hWords hClosed N bits (.state lower) pos hpos hCursor.2.2
    rw [dite_eq_right hz]
    by_cases he : a.same b = true
    · rw [dite_eq_left he]
      exact m.runCachedIndexed_trackedWordsBounded I tracked limit hWords hClosed N bits (.state upper) pos hpos hCursor.2.1
    rw [dite_eq_right he]
    by_cases hRead : pos < N
    · rw [dite_eq_left hRead]
      dsimp only
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · rw [ite_eq_left hd]
        exact m.runCachedIndexed_trackedWordsBounded I tracked limit hWords hClosed N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) hCursor
      · rw [ite_eq_right hd]
        apply m.runCachedIndexed_trackedWordsBounded I tracked limit hWords hClosed N bits _ (pos + 1) (by omega)
        cases hBit : bits ⟨pos, hRead⟩
        · exact hCursor.2.1
        · exact hCursor.2.2
    · rw [dite_eq_right hRead]
      trivial
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [hCursorEq, cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem runCached_trackedWordsBounded {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (tracked : S → Bool) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).TrackedWordsHeight tracked limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R : ℕ) (s : S) (hI : I s) (bits : Fin R → Bool) :
    m.CachedTrackedWordsBounded I tracked limit R bits (.state s) 0 (Nat.zero_le _) :=
  m.runCachedIndexed_trackedWordsBounded I tracked limit hWords hClosed R bits (.state s) 0 (Nat.zero_le _) hI

end Blotto.WordStateMachine
