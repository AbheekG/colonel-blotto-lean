import Blotto.CachedTrackedWordBounds
import Blotto.BinaryCoinWordWork

/-! Boolean word-body allowances for tracked coin phases follow the complete
production path. Untracked words keep their true values and add no charge.
Transition callbacks, encoding, tracking/index and physical costs are separate. -/

namespace Blotto.WordStateMachine

def cachedTrackedWordWork {S α : Type*} (m : WordStateMachine S α) (tracked : S → Bool) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done _ => 0
    | .ask a b hb hab upper lower => m.cachedTrackedWordWork tracked N bits (.ofWords a b hb hab upper lower) pos hpos
  | @CachedWordCursor.coin _ w a b hb hab upper lower =>
    (if trackedCoin tracked upper lower then FixedWordCoin.bodyAllowance w else 0) +
      if hz : a.isZero = true then m.cachedTrackedWordWork tracked N bits (.state lower) pos hpos else
      if he : a.same b = true then m.cachedTrackedWordWork tracked N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.cachedTrackedWordWork tracked N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.cachedTrackedWordWork tracked N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
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

theorem cachedTrackedWordWork_visits {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (tracked : S → Bool) (limit N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (h : m.CachedTrackedWordsBounded I tracked limit N bits cursor pos hpos) :
    m.cachedTrackedWordWork tracked N bits cursor pos hpos ≤
      FixedWordCoin.bodyAllowance limit * (m.cachedCounts N bits cursor pos hpos).visits := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at h
    unfold cachedTrackedWordWork cachedCounts
    unfold CachedTrackedWordsBounded at h
    cases hs : m.step s with
    | done value => exact Nat.zero_le _
    | ask a b hb hab upper lower =>
      rw [hs] at h
      have ih := m.cachedTrackedWordWork_visits I tracked limit N bits (.ofWords a b hb hab upper lower) pos hpos h.2
      simp only [ControllerCounts.withCallback]
      nlinarith
  | @coin w a b hb hab upper lower =>
    rw [hCursorEq] at h
    unfold cachedTrackedWordWork cachedCounts
    unfold CachedTrackedWordsBounded at h
    have hCharge : (if trackedCoin tracked upper lower then FixedWordCoin.bodyAllowance w else 0) ≤
        FixedWordCoin.bodyAllowance limit := by
      by_cases ht : trackedCoin tracked upper lower = true
      · rw [ite_eq_left ht]
        have hWidth := h.1 ht
        rw [FixedWordCoin.bodyAllowance_eq, FixedWordCoin.bodyAllowance_eq]
        omega
      · simp only [ite_eq_right ht]
        exact Nat.zero_le _
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz, ControllerCounts.withVisit] at h ⊢
      have ih := m.cachedTrackedWordWork_visits I tracked limit N bits (.state lower) pos hpos h.2
      nlinarith
    simp only [dite_eq_right hz] at h ⊢
    by_cases he : a.same b = true
    · simp only [dite_eq_left he, ControllerCounts.withVisit] at h ⊢
      have ih := m.cachedTrackedWordWork_visits I tracked limit N bits (.state upper) pos hpos h.2
      nlinarith
    simp only [dite_eq_right he] at h ⊢
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead] at h ⊢
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd, ControllerCounts.withRead] at h ⊢
        have ih := m.cachedTrackedWordWork_visits I tracked limit N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) h.2
        nlinarith
      · simp only [ite_eq_right hd, ControllerCounts.withRead] at h ⊢
        have ih := m.cachedTrackedWordWork_visits I tracked limit N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega) h.2
        nlinarith
    · simp only [dite_eq_right hRead, Nat.add_zero, Nat.mul_one]
      exact hCharge
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [hCursorEq, cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem runCachedTrackedWordWork_bound {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (tracked : S → Bool) (limit : ℕ)
    (hWords : ∀ s, I s → (m.step s).TrackedWordsHeight tracked limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedTrackedWordWork tracked R bits (.state s) 0 (Nat.zero_le _) ≤ (24 * limit + 28) * (2 * C + 2 * R + 2) := by
  have hp := m.runCached_trackedWordsBounded I tracked limit hWords hClosed R s hI bits
  have hw := m.cachedTrackedWordWork_visits I tracked limit R bits (.state s) 0 (Nat.zero_le _) hp
  have hc := (m.runCachedCounts_bounds R C s hRank bits).2
  rw [FixedWordCoin.bodyAllowance_eq] at hw
  exact hw.trans (Nat.mul_le_mul_left _ hc)

end Blotto.WordStateMachine
