import Blotto.WordMachineRefinement

/-! Operational labels for the indexed controller: callback queries, input
bit reads and cursor visits. The observer follows the loop's guards exactly.
It is a cost specification, not a second runtime sampler or a heap model. -/

namespace Blotto

structure ControllerCounts where
  callbacks : ℕ
  reads : ℕ
  visits : ℕ

namespace ControllerCounts

def withCallback (c : ControllerCounts) : ControllerCounts := ⟨c.callbacks + 1, c.reads, c.visits + 1⟩
def withVisit (c : ControllerCounts) : ControllerCounts := ⟨c.callbacks, c.reads, c.visits + 1⟩
def withRead (c : ControllerCounts) : ControllerCounts := ⟨c.callbacks, c.reads + 1, c.visits + 1⟩

end ControllerCounts

namespace WordStateMachine

def cursorCallbackBound {S α : Type*} (m : WordStateMachine S α) : WordCursor S → ℕ
  | .state s => m.rank s + 1
  | .coin _ _ _ _ upper lower => 1 + max (m.rank upper) (m.rank lower)

def indexedCounts {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ControllerCounts :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done _ => ⟨1, 0, 1⟩
    | .ask a b hb hab upper lower =>
      (m.indexedCounts N bits (.coin a b hb hab upper lower) pos hpos).withCallback
  | .coin a b hb hab upper lower =>
    if a = 0 then (m.indexedCounts N bits (.state lower) pos hpos).withVisit else
      if b ≤ a then (m.indexedCounts N bits (.state upper) pos hpos).withVisit else
        if hRead : pos < N then
          let bit := bits ⟨pos, hRead⟩
          if bit = denominatorDigit a b then
            (m.indexedCounts N bits
              (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega)).withRead
          else (m.indexedCounts N bits (.state (if bit then lower else upper)) (pos + 1) (by omega)).withRead
        else ⟨0, 0, 1⟩
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    omega
  all_goals omega

theorem indexedCounts_reads {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    pos + (m.indexedCounts N bits cursor pos hpos).reads = (m.runCursorIndexed N bits cursor pos hpos).2 := by
  cases cursor with
  | state s =>
    conv_lhs => unfold indexedCounts
    conv_rhs => unfold runCursorIndexed
    cases ht : m.step s with
    | done value => simp only [Nat.add_zero]
    | ask a b hb hab upper lower =>
      exact m.indexedCounts_reads N bits (.coin a b hb hab upper lower) pos hpos
  | coin a b hb hab upper lower =>
    conv_lhs => unfold indexedCounts
    conv_rhs => unfold runCursorIndexed
    by_cases ha : a = 0
    · simp only [ha, ite_true, ControllerCounts.withVisit]
      exact m.indexedCounts_reads N bits (.state lower) pos hpos
    by_cases hba : b ≤ a
    · simp only [ha, hba, ite_false, ite_true, ControllerCounts.withVisit]
      exact m.indexedCounts_reads N bits (.state upper) pos hpos
    simp only [ha, hba, ite_false]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a b
      · simp only [hd, ite_true, ControllerCounts.withRead]
        have h := m.indexedCounts_reads N bits
          (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega)
        omega
      · simp only [hd, ite_false, ControllerCounts.withRead]
        have h := m.indexedCounts_reads N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        omega
    · simp only [dite_eq_right hRead, Nat.add_zero]
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [ht] at hp
    omega
  all_goals omega

theorem indexedCounts_bounds {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    (m.indexedCounts N bits cursor pos hpos).callbacks ≤ m.cursorCallbackBound cursor ∧
      (m.indexedCounts N bits cursor pos hpos).visits ≤ m.cursorRank cursor + 2 * (N - pos) + 1 := by
  cases cursor with
  | state s =>
    unfold indexedCounts
    cases ht : m.step s with
    | done value => simp only [cursorCallbackBound, cursorRank]; constructor <;> omega
    | ask a b hb hab upper lower =>
      have h := m.indexedCounts_bounds N bits (.coin a b hb hab upper lower) pos hpos
      have hp := m.progress s
      rw [ht] at hp
      simp only [ControllerCounts.withCallback, cursorCallbackBound, cursorRank] at h ⊢
      constructor <;> omega
  | coin a b hb hab upper lower =>
    unfold indexedCounts
    by_cases ha : a = 0
    · simp only [ha, ite_true, ControllerCounts.withVisit, cursorCallbackBound, cursorRank]
      have h := m.indexedCounts_bounds N bits (.state lower) pos hpos
      simp only [cursorCallbackBound, cursorRank] at h
      constructor <;> omega
    by_cases hba : b ≤ a
    · simp only [ha, hba, ite_false, ite_true, ControllerCounts.withVisit, cursorCallbackBound, cursorRank]
      have h := m.indexedCounts_bounds N bits (.state upper) pos hpos
      simp only [cursorCallbackBound, cursorRank] at h
      constructor <;> omega
    simp only [ha, hba, ite_false]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a b
      · simp only [hd, ite_true, ControllerCounts.withRead, cursorCallbackBound, cursorRank]
        have h := m.indexedCounts_bounds N bits
          (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega)
        simp only [cursorCallbackBound, cursorRank] at h
        constructor <;> omega
      · simp only [hd, ite_false, ControllerCounts.withRead, cursorCallbackBound, cursorRank]
        have h := m.indexedCounts_bounds N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        by_cases hbit : bits ⟨pos, hRead⟩ = true
        · simp only [hbit, ite_true, cursorCallbackBound, cursorRank] at h ⊢
          constructor <;> omega
        · simp [hbit, cursorCallbackBound, cursorRank] at h ⊢
          constructor <;> omega
    · simp only [dite_eq_right hRead, cursorCallbackBound, cursorRank]
      constructor <;> omega
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [ht] at hp
    omega
  all_goals omega

def runCounts {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) : ControllerCounts :=
  m.indexedCounts R bits (.state s) 0 (Nat.zero_le R)

theorem runCounts_reads_eq {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    (m.runCounts R s bits).reads = (m.run R s bits).2 := by
  rw [m.run_eq_numeric]
  simpa only [runCounts, runNumeric, Nat.zero_add] using m.indexedCounts_reads R bits (.state s) 0 (Nat.zero_le R)

theorem runCounts_reads_le {S α : Type*} (m : WordStateMachine S α) (R : ℕ) (s : S) (bits : Fin R → Bool) :
    (m.runCounts R s bits).reads ≤ R := by
  rw [m.runCounts_reads_eq]
  exact m.run_bits_le R s bits

theorem runCounts_bounds {S α : Type*} (m : WordStateMachine S α) (R C : ℕ) (s : S)
    (hC : m.rank s ≤ C) (bits : Fin R → Bool) :
    (m.runCounts R s bits).callbacks ≤ C + 1 ∧ (m.runCounts R s bits).visits ≤ 2 * C + 2 * R + 2 := by
  have h := m.indexedCounts_bounds R bits (.state s) 0 (Nat.zero_le R)
  simp only [cursorCallbackBound, cursorRank, Nat.sub_zero] at h
  exact ⟨h.1.trans (by omega), h.2.trans (by omega)⟩

end WordStateMachine
end Blotto
