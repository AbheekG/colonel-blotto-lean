import Blotto.CachedWordControllerHeight
import Blotto.BinaryCoinWordWork

/-! Boolean word-body allowances compose on the production cached path.
Transition callbacks, encoding, index arithmetic and physical allocation are
priced separately; this ledger never constructs the specification tree. -/

namespace Blotto.WordStateMachine

def cachedWordWork {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done _ => 0
    | .ask a b hb hab upper lower => m.cachedWordWork N bits (.ofWords a b hb hab upper lower) pos hpos
  | @CachedWordCursor.coin _ w a b hb hab upper lower =>
    FixedWordCoin.bodyAllowance w +
      if hz : a.isZero = true then m.cachedWordWork N bits (.state lower) pos hpos else
      if he : a.same b = true then m.cachedWordWork N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.cachedWordWork N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.cachedWordWork N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
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

theorem cachedWordWork_visits {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (limit N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N)
    (h : m.CachedWordsBounded I limit N bits cursor pos hpos) :
    m.cachedWordWork N bits cursor pos hpos ≤
      FixedWordCoin.bodyAllowance limit * (m.cachedCounts N bits cursor pos hpos).visits := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at h
    unfold cachedWordWork cachedCounts
    unfold CachedWordsBounded at h
    cases hs : m.step s with
    | done value => exact Nat.zero_le _
    | ask a b hb hab upper lower =>
      rw [hs] at h
      have ih := m.cachedWordWork_visits I limit N bits (.ofWords a b hb hab upper lower) pos hpos h.2
      simp only [ControllerCounts.withCallback]
      nlinarith
  | @coin w a b hb hab upper lower =>
    rw [hCursorEq] at h
    unfold cachedWordWork cachedCounts
    unfold CachedWordsBounded at h
    have hCharge : FixedWordCoin.bodyAllowance w ≤ FixedWordCoin.bodyAllowance limit := by
      rw [FixedWordCoin.bodyAllowance_eq, FixedWordCoin.bodyAllowance_eq]
      omega
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz, ControllerCounts.withVisit] at h ⊢
      have ih := m.cachedWordWork_visits I limit N bits (.state lower) pos hpos h.2
      nlinarith
    simp only [dite_eq_right hz] at h ⊢
    by_cases he : a.same b = true
    · simp only [dite_eq_left he, ControllerCounts.withVisit] at h ⊢
      have ih := m.cachedWordWork_visits I limit N bits (.state upper) pos hpos h.2
      nlinarith
    simp only [dite_eq_right he] at h ⊢
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead] at h ⊢
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd, ControllerCounts.withRead] at h ⊢
        have ih := m.cachedWordWork_visits I limit N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) h.2
        nlinarith
      · simp only [ite_eq_right hd, ControllerCounts.withRead] at h ⊢
        have ih := m.cachedWordWork_visits I limit N bits
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

theorem runCachedWordWork_bound {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (limit : ℕ)
    (hWords : ∀ s, I s → (m.step s).WordsHeight limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R C : ℕ) (s : S) (hI : I s) (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.cachedWordWork R bits (.state s) 0 (Nat.zero_le _) ≤ (24 * limit + 28) * (2 * C + 2 * R + 2) := by
  have hp := m.runCached_wordsBounded I limit hWords hClosed R s hI bits
  have hw := m.cachedWordWork_visits I limit R bits (.state s) 0 (Nat.zero_le _) hp
  have hc := (m.runCachedCounts_bounds R C s hRank bits).2
  rw [FixedWordCoin.bodyAllowance_eq] at hw
  exact hw.trans (Nat.mul_le_mul_left _ hc)

end Blotto.WordStateMachine
