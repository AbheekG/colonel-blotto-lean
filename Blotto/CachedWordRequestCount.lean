import Blotto.CachedWordControllerCounts

/-! Coin encodings are new requests, not all state callbacks. The request
count is bounded by source rank even when an exhausted cap visits a coin. -/

namespace Blotto.WordStateMachine

def cachedRequestRank {S α : Type*} (m : WordStateMachine S α) : CachedWordCursor S → ℕ
  | .state s => m.rank s
  | .coin _ _ _ _ upper lower => max (m.rank upper) (m.rank lower)

def cachedRequests {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done _ => 0
    | .ask a b hb hab upper lower =>
      1 + m.cachedRequests N bits (.ofWords a b hb hab upper lower) pos hpos
  | .coin a b hb hab upper lower =>
    if hz : a.isZero = true then m.cachedRequests N bits (.state lower) pos hpos else
      if he : a.same b = true then m.cachedRequests N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.cachedRequests N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.cachedRequests N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
            (pos + 1) (by omega)
        else 0
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem cachedRequests_bound {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedRequests N bits cursor pos hpos ≤ m.cachedRequestRank cursor := by
  cases hCursorEq : cursor with
  | state s =>
    unfold cachedRequests
    cases hs : m.step s with
    | done value => exact Nat.zero_le _
    | ask a b hb hab upper lower =>
      change 1 + m.cachedRequests N bits (.ofWords a b hb hab upper lower) pos hpos ≤ m.cachedRequestRank (.state s)
      have ih := m.cachedRequests_bound N bits (.ofWords a b hb hab upper lower) pos hpos
      have hp := m.progress s
      rw [hs] at hp
      change m.cachedRequests N bits (.ofWords a b hb hab upper lower) pos hpos ≤
        max (m.rank upper) (m.rank lower) at ih
      change _ ≤ m.rank s
      omega
  | coin a b hb hab upper lower =>
    unfold cachedRequests
    change _ ≤ max (m.rank upper) (m.rank lower)
    by_cases hz : a.isZero = true
    · rw [dite_eq_left hz]
      exact (m.cachedRequests_bound N bits (.state lower) pos hpos).trans (le_max_right _ _)
    rw [dite_eq_right hz]
    by_cases he : a.same b = true
    · rw [dite_eq_left he]
      exact (m.cachedRequests_bound N bits (.state upper) pos hpos).trans (le_max_left _ _)
    rw [dite_eq_right he]
    by_cases hRead : pos < N
    · rw [dite_eq_left hRead]
      dsimp only
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · rw [ite_eq_left hd]
        exact m.cachedRequests_bound N bits (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower)
          (pos + 1) (by omega)
      · rw [ite_eq_right hd]
        have ih := m.cachedRequests_bound N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
          (pos + 1) (by omega)
        cases hbBit : bits ⟨pos, hRead⟩
        · rw [hbBit] at ih
          simpa only [Bool.false_eq_true, ite_false, cachedRequestRank] using ih.trans (le_max_left _ (m.rank lower))
        · rw [hbBit] at ih
          simpa only [ite_true, cachedRequestRank] using ih.trans (le_max_right (m.rank upper) _)
    · rw [dite_eq_right hRead]
      exact Nat.zero_le _
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem runCachedRequests_bound {S α : Type*} (m : WordStateMachine S α) (R C : ℕ) (s : S)
    (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedRequests R bits (.state s) 0 (Nat.zero_le _) ≤ C :=
  (m.cachedRequests_bound R bits (.state s) 0 (Nat.zero_le _)).trans hRank

end Blotto.WordStateMachine
