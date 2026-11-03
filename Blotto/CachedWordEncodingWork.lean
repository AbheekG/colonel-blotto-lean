import Blotto.CachedWordControllerWork
import Blotto.CachedWordRequestCount

/-! Encoding work is charged once at each new state request. Every numerator
and denominator emits exactly its cached width in payload bits. Pending coins
carry no encoding charge. Native testBit/width/backend prices remain separate. -/

namespace Blotto.WordStateMachine

def cachedEncodingCells {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done _ => 0
    | .ask a b hb hab upper lower =>
      2 * binaryWordWidth b + m.cachedEncodingCells N bits (.ofWords a b hb hab upper lower) pos hpos
  | .coin a b hb hab upper lower =>
    if hz : a.isZero = true then m.cachedEncodingCells N bits (.state lower) pos hpos else
      if he : a.same b = true then m.cachedEncodingCells N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.cachedEncodingCells N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.cachedEncodingCells N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
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

theorem cachedEncodingCells_callbacks {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (limit N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (h : m.CachedWordsBounded I limit N bits cursor pos hpos) :
    m.cachedEncodingCells N bits cursor pos hpos ≤ 2 * limit * (m.cachedCounts N bits cursor pos hpos).callbacks := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at h
    unfold cachedEncodingCells cachedCounts
    unfold CachedWordsBounded at h
    cases hs : m.step s with
    | done value => exact Nat.zero_le _
    | ask a b hb hab upper lower =>
      rw [hs] at h
      have hWidth : binaryWordWidth b ≤ limit := by
        have hCoin := h.2
        simp only [CachedWordCursor.ofWords] at hCoin
        conv at hCoin => unfold CachedWordsBounded
        exact hCoin.1
      have ih := m.cachedEncodingCells_callbacks I limit N bits (.ofWords a b hb hab upper lower) pos hpos h.2
      simp only [ControllerCounts.withCallback]
      nlinarith
  | coin a b hb hab upper lower =>
    rw [hCursorEq] at h
    unfold cachedEncodingCells cachedCounts
    unfold CachedWordsBounded at h
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz, ControllerCounts.withVisit] at h ⊢
      exact m.cachedEncodingCells_callbacks I limit N bits (.state lower) pos hpos h.2
    simp only [dite_eq_right hz] at h ⊢
    by_cases he : a.same b = true
    · simp only [dite_eq_left he, ControllerCounts.withVisit] at h ⊢
      exact m.cachedEncodingCells_callbacks I limit N bits (.state upper) pos hpos h.2
    simp only [dite_eq_right he] at h ⊢
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead] at h ⊢
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd, ControllerCounts.withRead] at h ⊢
        exact m.cachedEncodingCells_callbacks I limit N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) h.2
      · simp only [ite_eq_right hd, ControllerCounts.withRead] at h ⊢
        exact m.cachedEncodingCells_callbacks I limit N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega) h.2
    · simp only [dite_eq_right hRead]
      exact Nat.zero_le _
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [hCursorEq, cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem cachedEncodingCells_requests {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (limit N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (h : m.CachedWordsBounded I limit N bits cursor pos hpos) :
    m.cachedEncodingCells N bits cursor pos hpos ≤ 2 * limit * m.cachedRequests N bits cursor pos hpos := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at h
    unfold cachedEncodingCells cachedRequests
    unfold CachedWordsBounded at h
    cases hs : m.step s with
    | done value => exact Nat.zero_le _
    | ask a b hb hab upper lower =>
      rw [hs] at h
      have hWidth : binaryWordWidth b ≤ limit := by
        have hCoin := h.2
        simp only [CachedWordCursor.ofWords] at hCoin
        conv at hCoin => unfold CachedWordsBounded
        exact hCoin.1
      have ih := m.cachedEncodingCells_requests I limit N bits (.ofWords a b hb hab upper lower) pos hpos h.2
      dsimp only
      nlinarith
  | coin a b hb hab upper lower =>
    rw [hCursorEq] at h
    unfold cachedEncodingCells cachedRequests
    unfold CachedWordsBounded at h
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz] at h ⊢
      exact m.cachedEncodingCells_requests I limit N bits (.state lower) pos hpos h.2
    simp only [dite_eq_right hz] at h ⊢
    by_cases he : a.same b = true
    · simp only [dite_eq_left he] at h ⊢
      exact m.cachedEncodingCells_requests I limit N bits (.state upper) pos hpos h.2
    simp only [dite_eq_right he] at h ⊢
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead] at h ⊢
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd] at h ⊢
        exact m.cachedEncodingCells_requests I limit N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) h.2
      · simp only [ite_eq_right hd] at h ⊢
        exact m.cachedEncodingCells_requests I limit N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega) h.2
    · simp only [dite_eq_right hRead]
      exact Nat.zero_le _
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [hCursorEq, cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem runCachedEncodingCells_bound {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (limit : ℕ)
    (hWords : ∀ s, I s → (m.step s).WordsHeight limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedEncodingCells R bits (.state s) 0 (Nat.zero_le _) ≤ 2 * limit * (C + 1) := by
  have hp := m.runCached_wordsBounded I limit hWords hClosed R s hI bits
  have he := m.cachedEncodingCells_callbacks I limit R bits (.state s) 0 (Nat.zero_le _) hp
  exact he.trans (Nat.mul_le_mul_left _ (m.runCachedCounts_bounds R C s hRank bits).1)

theorem runCachedEncodingCells_rank_bound {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).WordsHeight limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedEncodingCells R bits (.state s) 0 (Nat.zero_le _) ≤ 2 * limit * C := by
  have hp := m.runCached_wordsBounded I limit hWords hClosed R s hI bits
  have he := m.cachedEncodingCells_requests I limit R bits (.state s) 0 (Nat.zero_le _) hp
  exact he.trans (Nat.mul_le_mul_left _ (m.runCachedRequests_bound R C s hRank bits))

-- One native bit extraction and one emitted payload cell per encoded bit.
def cachedPreparationAndWordWork {S α : Type*} (m : WordStateMachine S α) (R : ℕ)
    (s : S) (bits : Fin R → Bool) : ℕ :=
  2 * m.cachedEncodingCells R bits (.state s) 0 (Nat.zero_le _) +
    m.cachedWordWork R bits (.state s) 0 (Nat.zero_le _)

theorem runCachedPreparationAndWordWork_bound {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).WordsHeight limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedPreparationAndWordWork R s bits ≤
      4 * limit * (C + 1) + (24 * limit + 28) * (2 * C + 2 * R + 2) := by
  have he := m.runCachedEncodingCells_bound I limit hWords hClosed R C s hI hRank bits
  have hw := m.runCachedWordWork_bound I limit hWords hClosed R C s hI hRank bits
  unfold cachedPreparationAndWordWork
  nlinarith

theorem runCachedPreparationAndWordWork_rank_bound {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).WordsHeight limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedPreparationAndWordWork R s bits ≤
      4 * limit * C + (24 * limit + 28) * (2 * C + 2 * R + 2) := by
  have he := m.runCachedEncodingCells_rank_bound I limit hWords hClosed R C s hI hRank bits
  have hw := m.runCachedWordWork_bound I limit hWords hClosed R C s hI hRank bits
  unfold cachedPreparationAndWordWork
  nlinarith

end Blotto.WordStateMachine
