import Blotto.FixedWordCoin

/-! The Boolean-word coin has the exact old result and consumed input count,
so all old probability, failure, moment and error contracts transfer. -/

namespace Blotto.FixedWordCoin

theorem numericTerminalHead (K : ℕ) (bits : Fin K → Bool) (v : Bool) :
    numericTerminalMachine.runCursor K (.state v) bits = (some v, 0) := by
  conv_lhs => unfold WordStateMachine.runCursor
  rfl

theorem numericCoinHead (K a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (bits : Fin K → Bool) :
    numericTerminalMachine.runCursor K (.coin a b hb hab true false) bits = runFixedDenominatorCoin K a b bits := by
  induction K generalizing a with
  | zero =>
    conv_lhs => unfold WordStateMachine.runCursor
    conv_rhs => unfold runFixedDenominatorCoin
    by_cases hz : a = 0
    · simp only [ite_eq_left hz, numericTerminalHead]
    · simp only [ite_eq_right hz]
      by_cases he : b ≤ a
      · simp only [ite_eq_left he, numericTerminalHead]
      · simp only [ite_eq_right he]
  | succ K ih =>
    conv_lhs => unfold WordStateMachine.runCursor
    conv_rhs => unfold runFixedDenominatorCoin
    by_cases hz : a = 0
    · simp only [ite_eq_left hz, numericTerminalHead]
    · simp only [ite_eq_right hz]
      by_cases he : b ≤ a
      · simp only [ite_eq_left he, numericTerminalHead]
      · simp only [ite_eq_right he]
        by_cases hd : bits 0 = denominatorDigit a b
        · simp only [ite_eq_left hd]
          rw [ih _ (numeratorResidual_bounds a b hab)]
        · simp only [ite_eq_right hd, numericTerminalHead]
          cases hBit : bits 0 <;> rfl

theorem run_refines {w : ℕ} (K : ℕ) (a b : FixedBinaryWord w) (hb : 0 < b.value)
    (hab : a.value ≤ b.value) (bits : Fin K → Bool) :
    run K a b hb hab bits = runFixedDenominatorCoin K a.value b.value bits := by
  rw [run, runIndexed_refines, WordStateMachine.runCursorIndexed_zero, numericCoinHead]

theorem run_bits_le {w : ℕ} (K : ℕ) (a b : FixedBinaryWord w) (hb : 0 < b.value)
    (hab : a.value ≤ b.value) (bits : Fin K → Bool) : (run K a b hb hab bits).2 ≤ K := by
  rw [run_refines]
  exact runFixedDenominatorCoin_bits_le _ _ _ hb bits

theorem run_failure_probability {w : ℕ} (K : ℕ) (a b : FixedBinaryWord w) (hb : 0 < b.value)
    (hab : a.value ≤ b.value) :
    (fairBitLaw K : MeasureTheory.Measure (Fin K → Bool)).real
      {bits | (run K a b hb hab bits).1 = none} ≤ 1 / (2 : ℝ) ^ K := by
  simp only [run_refines]
  exact runFixedDenominatorCoin_failure_probability _ _ _ hb

theorem run_true_error {w : ℕ} (K : ℕ) (a b : FixedBinaryWord w) (hb : 0 < b.value)
    (hab : a.value ≤ b.value) :
    |(fairBitLaw K : MeasureTheory.Measure (Fin K → Bool)).real
      {bits | (run K a b hb hab bits).1 = some true} - ((a.value : ℝ) / b.value)| ≤ 1 / (2 : ℝ) ^ K := by
  simp only [run_refines]
  exact runFixedDenominatorCoin_true_error _ _ _ hb hab

theorem run_moment {w : ℕ} (K : ℕ) (a b : FixedBinaryWord w) (hb : 0 < b.value)
    (hab : a.value ≤ b.value) :
    (∫ bits, (4 / 3 : ℝ) ^ (run K a b hb hab bits).2 ∂(fairBitLaw K : MeasureTheory.Measure (Fin K → Bool))) ≤ 2 := by
  simp only [run_refines]
  exact runFixedDenominatorCoin_moment _ _ _ hb

end Blotto.FixedWordCoin
