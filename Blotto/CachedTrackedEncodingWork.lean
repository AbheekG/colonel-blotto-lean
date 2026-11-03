import Blotto.CachedTrackedWordWork
import Blotto.CachedWordRequestCount

/-! New tracked requests alone pay for Boolean payload encoding. The complete
production path is followed, including all untracked continuations and caps.
Native bit extraction, index and physical backend prices are separate. -/

namespace Blotto.WordStateMachine

def cachedTrackedEncodingCells {S α : Type*} (m : WordStateMachine S α) (tracked : S → Bool) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done _ => 0
    | .ask a b hb hab upper lower =>
      (if trackedCoin tracked upper lower then 2 * binaryWordWidth b else 0) + m.cachedTrackedEncodingCells tracked N bits (.ofWords a b hb hab upper lower) pos hpos
  | .coin a b hb hab upper lower =>
    if hz : a.isZero = true then m.cachedTrackedEncodingCells tracked N bits (.state lower) pos hpos else
      if he : a.same b = true then m.cachedTrackedEncodingCells tracked N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.cachedTrackedEncodingCells tracked N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.cachedTrackedEncodingCells tracked N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
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

theorem cachedTrackedEncodingCells_callbacks {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (tracked : S → Bool) (limit N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (h : m.CachedTrackedWordsBounded I tracked limit N bits cursor pos hpos) :
    m.cachedTrackedEncodingCells tracked N bits cursor pos hpos ≤ 2 * limit * (m.cachedCounts N bits cursor pos hpos).callbacks := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at h
    unfold cachedTrackedEncodingCells cachedCounts
    unfold CachedTrackedWordsBounded at h
    cases hs : m.step s with
    | done value => exact Nat.zero_le _
    | ask a b hb hab upper lower =>
      rw [hs] at h
      have hEncoding : (if trackedCoin tracked upper lower then 2 * binaryWordWidth b else 0) ≤ 2 * limit := by
        by_cases ht : trackedCoin tracked upper lower = true
        · rw [ite_eq_left ht]
          have hCoin := h.2
          simp only [CachedWordCursor.ofWords] at hCoin
          conv at hCoin => unfold CachedTrackedWordsBounded
          have hWidth := hCoin.1 ht
          omega
        · simp only [ite_eq_right ht]
          exact Nat.zero_le _
      have ih := m.cachedTrackedEncodingCells_callbacks I tracked limit N bits (.ofWords a b hb hab upper lower) pos hpos h.2
      simp only [ControllerCounts.withCallback]
      nlinarith
  | coin a b hb hab upper lower =>
    rw [hCursorEq] at h
    unfold cachedTrackedEncodingCells cachedCounts
    unfold CachedTrackedWordsBounded at h
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz, ControllerCounts.withVisit] at h ⊢
      exact m.cachedTrackedEncodingCells_callbacks I tracked limit N bits (.state lower) pos hpos h.2
    simp only [dite_eq_right hz] at h ⊢
    by_cases he : a.same b = true
    · simp only [dite_eq_left he, ControllerCounts.withVisit] at h ⊢
      exact m.cachedTrackedEncodingCells_callbacks I tracked limit N bits (.state upper) pos hpos h.2
    simp only [dite_eq_right he] at h ⊢
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead] at h ⊢
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd, ControllerCounts.withRead] at h ⊢
        exact m.cachedTrackedEncodingCells_callbacks I tracked limit N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) h.2
      · simp only [ite_eq_right hd, ControllerCounts.withRead] at h ⊢
        exact m.cachedTrackedEncodingCells_callbacks I tracked limit N bits
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

theorem cachedTrackedEncodingCells_requests {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (tracked : S → Bool) (limit N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (h : m.CachedTrackedWordsBounded I tracked limit N bits cursor pos hpos) :
    m.cachedTrackedEncodingCells tracked N bits cursor pos hpos ≤ 2 * limit * m.cachedRequests N bits cursor pos hpos := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at h
    unfold cachedTrackedEncodingCells cachedRequests
    unfold CachedTrackedWordsBounded at h
    cases hs : m.step s with
    | done value => exact Nat.zero_le _
    | ask a b hb hab upper lower =>
      rw [hs] at h
      have hEncoding : (if trackedCoin tracked upper lower then 2 * binaryWordWidth b else 0) ≤ 2 * limit := by
        by_cases ht : trackedCoin tracked upper lower = true
        · rw [ite_eq_left ht]
          have hCoin := h.2
          simp only [CachedWordCursor.ofWords] at hCoin
          conv at hCoin => unfold CachedTrackedWordsBounded
          have hWidth := hCoin.1 ht
          omega
        · simp only [ite_eq_right ht]
          exact Nat.zero_le _
      have ih := m.cachedTrackedEncodingCells_requests I tracked limit N bits (.ofWords a b hb hab upper lower) pos hpos h.2
      dsimp only
      nlinarith
  | coin a b hb hab upper lower =>
    rw [hCursorEq] at h
    unfold cachedTrackedEncodingCells cachedRequests
    unfold CachedTrackedWordsBounded at h
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz] at h ⊢
      exact m.cachedTrackedEncodingCells_requests I tracked limit N bits (.state lower) pos hpos h.2
    simp only [dite_eq_right hz] at h ⊢
    by_cases he : a.same b = true
    · simp only [dite_eq_left he] at h ⊢
      exact m.cachedTrackedEncodingCells_requests I tracked limit N bits (.state upper) pos hpos h.2
    simp only [dite_eq_right he] at h ⊢
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead] at h ⊢
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd] at h ⊢
        exact m.cachedTrackedEncodingCells_requests I tracked limit N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) h.2
      · simp only [ite_eq_right hd] at h ⊢
        exact m.cachedTrackedEncodingCells_requests I tracked limit N bits
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

theorem runCachedTrackedEncodingCells_bound {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (tracked : S → Bool) (limit : ℕ)
    (hWords : ∀ s, I s → (m.step s).TrackedWordsHeight tracked limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedTrackedEncodingCells tracked R bits (.state s) 0 (Nat.zero_le _) ≤ 2 * limit * (C + 1) := by
  have hp := m.runCached_trackedWordsBounded I tracked limit hWords hClosed R s hI bits
  have he := m.cachedTrackedEncodingCells_callbacks I tracked limit R bits (.state s) 0 (Nat.zero_le _) hp
  exact he.trans (Nat.mul_le_mul_left _ (m.runCachedCounts_bounds R C s hRank bits).1)

theorem runCachedTrackedEncodingCells_rank_bound {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (tracked : S → Bool) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).TrackedWordsHeight tracked limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedTrackedEncodingCells tracked R bits (.state s) 0 (Nat.zero_le _) ≤ 2 * limit * C := by
  have hp := m.runCached_trackedWordsBounded I tracked limit hWords hClosed R s hI bits
  have he := m.cachedTrackedEncodingCells_requests I tracked limit R bits (.state s) 0 (Nat.zero_le _) hp
  exact he.trans (Nat.mul_le_mul_left _ (m.runCachedRequests_bound R C s hRank bits))

-- One native bit extraction and one emitted payload cell per encoded bit.
def cachedTrackedPreparationAndWordWork {S α : Type*} (m : WordStateMachine S α) (tracked : S → Bool) (R : ℕ)
    (s : S) (bits : Fin R → Bool) : ℕ :=
  2 * m.cachedTrackedEncodingCells tracked R bits (.state s) 0 (Nat.zero_le _) +
    m.cachedTrackedWordWork tracked R bits (.state s) 0 (Nat.zero_le _)

theorem runCachedTrackedPreparationAndWordWork_bound {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (tracked : S → Bool) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).TrackedWordsHeight tracked limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedTrackedPreparationAndWordWork tracked R s bits ≤
      4 * limit * (C + 1) + (24 * limit + 28) * (2 * C + 2 * R + 2) := by
  have he := m.runCachedTrackedEncodingCells_bound I tracked limit hWords hClosed R C s hI hRank bits
  have hw := m.runCachedTrackedWordWork_bound I tracked limit hWords hClosed R C s hI hRank bits
  unfold cachedTrackedPreparationAndWordWork
  nlinarith

theorem runCachedTrackedPreparationAndWordWork_rank_bound {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (tracked : S → Bool) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).TrackedWordsHeight tracked limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedTrackedPreparationAndWordWork tracked R s bits ≤
      4 * limit * C + (24 * limit + 28) * (2 * C + 2 * R + 2) := by
  have he := m.runCachedTrackedEncodingCells_rank_bound I tracked limit hWords hClosed R C s hI hRank bits
  have hw := m.runCachedTrackedWordWork_bound I tracked limit hWords hClosed R C s hI hRank bits
  unfold cachedTrackedPreparationAndWordWork
  nlinarith

end Blotto.WordStateMachine
