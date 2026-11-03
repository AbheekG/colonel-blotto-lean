import Blotto.WordMachineIndexedCounts

/-! Weighted callback-body work on the actual indexed fair-bit controller.
Coin iterations carry no callback charge, and exhausted input performs no
subsequent callback. The observer is separate from production sampling. -/

namespace Blotto.WordStateMachine

def indexedCallbackWork {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .state s => charge s + match _hs : m.step s with
    | .done _ => 0
    | .ask a b hb hab upper lower => m.indexedCallbackWork charge N bits (.coin a b hb hab upper lower) pos hpos
  | .coin a b hb hab upper lower =>
    if a = 0 then m.indexedCallbackWork charge N bits (.state lower) pos hpos else
      if b ≤ a then m.indexedCallbackWork charge N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let bit := bits ⟨pos, hRead⟩
          if bit = denominatorDigit a b then
            m.indexedCallbackWork charge N bits
              (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega)
          else m.indexedCallbackWork charge N bits (.state (if bit then lower else upper)) (pos + 1) (by omega)
        else 0
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    omega
  all_goals omega

theorem indexedCallbackWork_counts {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (bound : ℕ) (hCharge : ∀ s, charge s ≤ bound) (N : ℕ) (bits : Fin N → Bool)
    (cursor : WordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.indexedCallbackWork charge N bits cursor pos hpos ≤ bound * (m.indexedCounts N bits cursor pos hpos).callbacks := by
  cases cursor with
  | state s =>
    conv_lhs => unfold indexedCallbackWork
    conv_rhs => unfold indexedCounts
    cases ht : m.step s with
    | done value => simpa only [Nat.add_zero, Nat.mul_one] using hCharge s
    | ask a b hb hab upper lower =>
      have h := m.indexedCallbackWork_counts charge bound hCharge N bits (.coin a b hb hab upper lower) pos hpos
      have hc := hCharge s
      simp only [ControllerCounts.withCallback]
      nlinarith
  | coin a b hb hab upper lower =>
    conv_lhs => unfold indexedCallbackWork
    conv_rhs => unfold indexedCounts
    by_cases ha : a = 0
    · simp only [ha, ite_true, ControllerCounts.withVisit]
      exact m.indexedCallbackWork_counts charge bound hCharge N bits (.state lower) pos hpos
    by_cases hba : b ≤ a
    · simp only [ha, hba, ite_false, ite_true, ControllerCounts.withVisit]
      exact m.indexedCallbackWork_counts charge bound hCharge N bits (.state upper) pos hpos
    simp only [ha, hba, ite_false]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a b
      · simp only [hd, ite_true, ControllerCounts.withRead]
        exact m.indexedCallbackWork_counts charge bound hCharge N bits
          (.coin (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (pos + 1) (by omega)
      · simp only [hd, ite_false, ControllerCounts.withRead]
        exact m.indexedCallbackWork_counts charge bound hCharge N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
    · simp only [dite_eq_right hRead]
      exact Nat.zero_le _
termination_by (N - pos, m.cursorRank cursor)
decreasing_by
  all_goals simp only [cursorRank]
  · have hp := m.progress s
    rw [ht] at hp
    omega
  all_goals omega

def runCallbackWork {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (R : ℕ) (s : S) (bits : Fin R → Bool) : ℕ :=
  m.indexedCallbackWork charge R bits (.state s) 0 (Nat.zero_le R)

theorem runCallbackWork_bound {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (bound : ℕ) (hCharge : ∀ s, charge s ≤ bound) (R C : ℕ) (s : S)
    (hRank : m.rank s ≤ C) (bits : Fin R → Bool) :
    m.runCallbackWork charge R s bits ≤ bound * (C + 1) :=
  (m.indexedCallbackWork_counts charge bound hCharge R bits (.state s) 0 (Nat.zero_le _)).trans
    (Nat.mul_le_mul_left bound (m.runCounts_bounds R C s hRank bits).1)

theorem runCallbackWork_zero_initial_rank {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (bound : ℕ) (hCharge : ∀ s, charge s ≤ bound) (R : ℕ) (s : S) (hZero : charge s = 0)
    (bits : Fin R → Bool) : m.runCallbackWork charge R s bits ≤ bound * m.rank s := by
  unfold runCallbackWork
  unfold indexedCallbackWork
  rw [hZero, Nat.zero_add]
  cases ht : m.step s with
  | done value => exact Nat.zero_le _
  | ask a b hb hab upper lower =>
    have hw := m.indexedCallbackWork_counts charge bound hCharge R bits
      (.coin a b hb hab upper lower) 0 (Nat.zero_le _)
    have hc := (m.indexedCounts_bounds R bits (.coin a b hb hab upper lower) 0 (Nat.zero_le _)).1
    have hp := m.progress s
    rw [ht] at hp
    simp only [cursorCallbackBound] at hc
    have hUpper : m.rank upper + 1 ≤ m.rank s := by omega
    have hLower : m.rank lower + 1 ≤ m.rank s := by omega
    have hMax : 1 + max (m.rank upper) (m.rank lower) ≤ m.rank s := by omega
    exact hw.trans (Nat.mul_le_mul_left bound (hc.trans hMax))

end Blotto.WordStateMachine
