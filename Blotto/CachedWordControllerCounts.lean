import Blotto.WordMachineIndexedCounts

/-! Callback/read/visit labels follow the primary cached Boolean loop.
They equal the retained numeric observer exactly, including cap exhaustion. -/

namespace Blotto.WordStateMachine

def cachedCounts {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ControllerCounts :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done _ => ⟨1, 0, 1⟩
    | .ask a b hb hab upper lower =>
      (m.cachedCounts N bits (.ofWords a b hb hab upper lower) pos hpos).withCallback
  | .coin a b hb hab upper lower =>
    if hz : a.isZero = true then (m.cachedCounts N bits (.state lower) pos hpos).withVisit else
      if he : a.same b = true then (m.cachedCounts N bits (.state upper) pos hpos).withVisit else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            (m.cachedCounts N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)).withRead
          else (m.cachedCounts N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
            (pos + 1) (by omega)).withRead
        else ⟨0, 0, 1⟩
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem cachedCounts_refines {S α : Type*} (m : WordStateMachine S α) (N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCounts N bits cursor pos hpos = m.indexedCounts N bits cursor.reference pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => unfold cachedCounts
    conv_rhs => rw [CachedWordCursor.reference]; unfold indexedCounts
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      have h := m.cachedCounts_refines N bits (.ofWords a b hb hab upper lower) pos hpos
      simpa only [CachedWordCursor.reference_ofWords] using congrArg ControllerCounts.withCallback h
  | coin a b hb hab upper lower =>
    conv_lhs => unfold cachedCounts
    conv_rhs => rw [CachedWordCursor.reference]; unfold indexedCounts
    have hZero : a.isZero = true ↔ a.value = 0 := a.isZero_value
    have hSame : a.same b = true ↔ b.value ≤ a.value := by
      rw [a.same_value b]
      constructor
      · intro he; rw [he]
      · intro he; exact Nat.le_antisymm hab he
    simp only [hZero, hSame]
    by_cases hz : a.value = 0
    · simp only [dite_eq_left hz, ite_eq_left hz]
      exact congrArg ControllerCounts.withVisit (m.cachedCounts_refines N bits (.state lower) pos hpos)
    · simp only [dite_eq_right hz, ite_eq_right hz]
      by_cases he : b.value ≤ a.value
      · simp only [dite_eq_left he, ite_eq_left he]
        exact congrArg ControllerCounts.withVisit (m.cachedCounts_refines N bits (.state upper) pos hpos)
      · simp only [dite_eq_right he, ite_eq_right he]
        by_cases hRead : pos < N
        · simp only [dite_eq_left hRead, FixedBinaryWord.coinStep_digit]
          have hlt : a.value < b.value := lt_of_not_ge he
          by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a.value b.value
          · simp only [ite_eq_left hd]
            have h := m.cachedCounts_refines N bits
              (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
            simpa only [CachedWordCursor.reference, a.coinStep_residual b hlt] using congrArg ControllerCounts.withRead h
          · simp only [ite_eq_right hd]
            exact congrArg ControllerCounts.withRead
              (m.cachedCounts_refines N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega))
        · simp only [dite_eq_right hRead]
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

def runCachedCounts {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) : ControllerCounts :=
  m.cachedCounts R bits (.state s) 0 (Nat.zero_le R)

theorem runCachedCounts_eq {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    m.runCachedCounts R s bits = m.runCounts R s bits := m.cachedCounts_refines R bits (.state s) 0 (Nat.zero_le R)

theorem runCachedCounts_bounds {S α : Type*} (m : WordStateMachine S α) (R C : ℕ) (s : S)
    (hC : m.rank s ≤ C) (bits : Fin R → Bool) :
    (m.runCachedCounts R s bits).callbacks ≤ C + 1 ∧ (m.runCachedCounts R s bits).visits ≤ 2 * C + 2 * R + 2 := by
  rw [m.runCachedCounts_eq]
  exact m.runCounts_bounds R C s hC bits

theorem runCachedCounts_reads_eq {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    (m.runCachedCounts R s bits).reads = (m.run R s bits).2 := by
  rw [m.runCachedCounts_eq]
  exact m.runCounts_reads_eq R s bits

end Blotto.WordStateMachine
