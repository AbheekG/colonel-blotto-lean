import Blotto.CachedControlWork

/-! The single work observer equals the independently established Boolean
encoding-cell and coin-body ledgers at their documented primitive prices. -/

namespace Blotto.WordStateMachine

theorem cachedControlWork_prices_refine {S α : Type*} (m : WordStateMachine S α)
    (tracked : S → Bool) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedControlWork tracked (fun w => 4 * w) FixedWordCoin.bodyAllowance N bits cursor pos hpos =
      2 * m.cachedTrackedEncodingCells tracked N bits cursor pos hpos +
        m.cachedTrackedWordWork tracked N bits cursor pos hpos := by
  cases cursor with
  | state s =>
    conv_lhs => unfold cachedControlWork
    conv_rhs => unfold cachedTrackedEncodingCells; unfold cachedTrackedWordWork
    cases hs : m.step s with
    | done value => rfl
    | ask a b hb hab upper lower =>
      have ih := m.cachedControlWork_prices_refine tracked N bits (.ofWords a b hb hab upper lower) pos hpos
      by_cases ht : trackedCoin tracked upper lower = true
      · simp only [ite_eq_left ht]
        omega
      · simp only [ite_eq_right ht]
        omega
  | @coin w a b hb hab upper lower =>
    conv_lhs => unfold cachedControlWork
    conv_rhs => unfold cachedTrackedEncodingCells; unfold cachedTrackedWordWork
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      have ih := m.cachedControlWork_prices_refine tracked N bits (.state lower) pos hpos
      omega
    simp only [dite_eq_right hz]
    by_cases he : a.same b = true
    · simp only [dite_eq_left he]
      have ih := m.cachedControlWork_prices_refine tracked N bits (.state upper) pos hpos
      omega
    simp only [dite_eq_right he]
    by_cases hRead : pos < N
    · simp only [dite_eq_left hRead]
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · simp only [ite_eq_left hd]
        have ih := m.cachedControlWork_prices_refine tracked N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega)
        omega
      · simp only [ite_eq_right hd]
        have ih := m.cachedControlWork_prices_refine tracked N bits
          (.state (if bits ⟨pos, hRead⟩ then lower else upper)) (pos + 1) (by omega)
        omega
    · simp only [dite_eq_right hRead]
      omega
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [cachedCursorRank]
  all_goals first
    | (have hp := m.progress s; rw [hs] at hp; simp only [CachedWordCursor.ofWords]; omega)
    | omega

end Blotto.WordStateMachine
