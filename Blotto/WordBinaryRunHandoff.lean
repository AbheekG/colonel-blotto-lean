import Blotto.WordMachineChoice
import Blotto.WordMachineSerialRun
import Blotto.BinaryStoredCoinIndexed

/-! A binary root coin and its selected continuation share one reader/cap.
The exact equation retains exhaustion and absolute positions, including zero
and one probabilities; no independently capped branch sampler is substituted. -/

namespace Blotto

def binarySelectedCoin (words : ProbabilityWords) : WordCursor Bool:=
  .coin words.numerator words.denominator words.denominator_pos words.normalized true false

namespace WordStateMachine

theorem binary_coin_handoff {S T α : Type*} (words : ProbabilityWords) (upper : WordStateMachine S α)
  (lower : WordStateMachine T α) (upperStart : S) (lowerStart : T) (N : ℕ) (bits : Fin N→Bool)
  (a b : ℕ) (hb : 0<b) (hab : a≤b) (pos : ℕ) (hpos : pos≤N) :
  (binaryMachine words upper lower upperStart lowerStart).runCursorIndexed N bits
    (.coin a b hb hab (.upper upperStart) (.lower lowerStart)) pos hpos=
    handoff N (BinaryStoredCoinIndexed.selected.runCursorIndexed N bits (.coin a b hb hab true false) pos hpos)
      (fun branch pos hp=>if branch then upper.runCursorIndexed N bits (.state upperStart) pos hp
        else lower.runCursorIndexed N bits (.state lowerStart) pos hp):=by
  conv_lhs=>unfold runCursorIndexed
  conv_rhs=>arg 2;unfold runCursorIndexed
  by_cases hz : a=0
  · simp only [hz,ite_true,BinaryStoredCoinIndexed.selected_run,handoff,hpos,dite_true,Bool.false_eq_true,ite_false]
    exact embedding_runCursorIndexed lower (binaryMachine words upper lower upperStart lowerStart) BinaryState.lower
      (fun _=>rfl) N bits (.state lowerStart) pos hpos
  · simp only [hz,ite_false]
    by_cases he : b≤a
    · simp only [he,ite_true,BinaryStoredCoinIndexed.selected_run,handoff,hpos,dite_true,ite_true]
      exact embedding_runCursorIndexed upper (binaryMachine words upper lower upperStart lowerStart) BinaryState.upper
        (fun _=>rfl) N bits (.state upperStart) pos hpos
    · simp only [he,ite_false]
      by_cases hRead : pos<N
      · simp only [dite_eq_left hRead]
        by_cases hd : bits ⟨pos,hRead⟩=denominatorDigit a b
        · simp only [hd,ite_true]
          exact binary_coin_handoff words upper lower upperStart lowerStart N bits
            (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) (pos+1) (by omega)
        · simp only [hd,ite_false]
          cases hBit : bits ⟨pos,hRead⟩
          · simp only [Bool.false_eq_true,ite_false,BinaryStoredCoinIndexed.selected_run,handoff,ite_true]
            rw [dite_eq_left (show pos+1≤N by omega)]
            exact embedding_runCursorIndexed upper (binaryMachine words upper lower upperStart lowerStart) BinaryState.upper
              (fun _=>rfl) N bits (.state upperStart) (pos+1) (by omega)
          · simp only [ite_true,BinaryStoredCoinIndexed.selected_run,handoff,Bool.false_eq_true,ite_false]
            rw [dite_eq_left (show pos+1≤N by omega)]
            exact embedding_runCursorIndexed lower (binaryMachine words upper lower upperStart lowerStart) BinaryState.lower
              (fun _=>rfl) N bits (.state lowerStart) (pos+1) (by omega)
      · simp only [dite_eq_right hRead,handoff]
termination_by N-pos

theorem binary_root_handoff {S T α : Type*} (words : ProbabilityWords) (upper : WordStateMachine S α)
    (lower : WordStateMachine T α) (upperStart : S) (lowerStart : T) (N : ℕ) (bits : Fin N→Bool)
    (pos : ℕ) (hpos : pos≤N) :
    (binaryMachine words upper lower upperStart lowerStart).runCursorIndexed N bits (.state .start) pos hpos=
      handoff N (BinaryStoredCoinIndexed.selected.runCursorIndexed N bits (binarySelectedCoin words) pos hpos)
        (fun branch pos hp=>if branch then upper.runCursorIndexed N bits (.state upperStart) pos hp
          else lower.runCursorIndexed N bits (.state lowerStart) pos hp):=by
  conv_lhs=>unfold runCursorIndexed
  change (binaryMachine words upper lower upperStart lowerStart).runCursorIndexed N bits
    (.coin words.numerator words.denominator words.denominator_pos words.normalized (.upper upperStart) (.lower lowerStart)) pos hpos=_
  exact binary_coin_handoff words upper lower upperStart lowerStart N bits words.numerator words.denominator
    words.denominator_pos words.normalized pos hpos

end WordStateMachine
end Blotto
