import Blotto.FixedBinaryWord
import Blotto.WordMachineIndexedCoreRefinement

/-! A fixed-reader, tail-recursive fair-bit coin operates on Boolean words.
Between input bits it performs no large-natural arithmetic or fraction
reduction. Width and probability value are proof specifications. -/

namespace Blotto.FixedWordCoin

def runIndexed {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (_hpos : pos ≤ N)
    (a b : FixedBinaryWord w) (hb : 0 < b.value) (hab : a.value ≤ b.value) : Option Bool × ℕ :=
  if hz : a.isZero = true then (some false, pos) else
    if he : a.same b = true then (some true, pos) else
      if hRead : pos < N then
        let next := a.coinStep b
        have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
        let bit := bits ⟨pos, hRead⟩
        if bit = next.1 then runIndexed N bits (pos + 1) (by omega) next.2 b hb
          (a.coinStep_normalized b hlt).le
        else (some (!bit), pos + 1)
      else (none, pos)
termination_by N - pos
decreasing_by omega

def numericTerminalMachine : WordStateMachine Bool Bool where
  step := WordTransition.done
  rank := fun _ => 0
  progress := fun _ => trivial

theorem numericTerminal {N : ℕ} (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) (v : Bool) :
    numericTerminalMachine.runCursorIndexed N bits (.state v) pos hpos = (some v, pos) := by
  conv_lhs => unfold WordStateMachine.runCursorIndexed
  rfl

theorem runIndexed_refines {w : ℕ} (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N)
    (a b : FixedBinaryWord w) (hb : 0 < b.value) (hab : a.value ≤ b.value) :
    runIndexed N bits pos hpos a b hb hab =
      numericTerminalMachine.runCursorIndexed N bits (.coin a.value b.value hb hab true false) pos hpos := by
  conv_lhs => unfold runIndexed
  conv_rhs => unfold WordStateMachine.runCursorIndexed
  have hZero : a.isZero = true ↔ a.value = 0 := a.isZero_value
  have hSame : a.same b = true ↔ b.value ≤ a.value := by
    rw [a.same_value b]
    constructor
    · intro he; rw [he]
    · intro he; exact Nat.le_antisymm hab he
  simp only [hZero, hSame]
  by_cases hz : a.value = 0
  · simp only [dite_eq_left hz, ite_eq_left hz, numericTerminal]
  · simp only [dite_eq_right hz, ite_eq_right hz]
    by_cases he : b.value ≤ a.value
    · simp only [dite_eq_left he, ite_eq_left he, numericTerminal]
    · simp only [dite_eq_right he, ite_eq_right he]
      by_cases hRead : pos < N
      · simp only [dite_eq_left hRead]
        have hlt : a.value < b.value := lt_of_not_ge he
        simp only [FixedBinaryWord.coinStep_digit]
        by_cases hd : bits ⟨pos, hRead⟩ = denominatorDigit a.value b.value
        · simp only [ite_eq_left hd]
          have hi := runIndexed_refines N bits (pos + 1) (by omega) (a.coinStep b).2 b hb
            (a.coinStep_normalized b hlt).le
          rw [hi]
          simp only [a.coinStep_residual b hlt]
        · simp only [ite_eq_right hd, numericTerminal]
          cases hBit : bits ⟨pos, hRead⟩ <;> rfl
      · simp only [dite_eq_right hRead]
termination_by N - pos
decreasing_by omega

def run {w : ℕ} (K : ℕ) (a b : FixedBinaryWord w) (hb : 0 < b.value)
    (hab : a.value ≤ b.value) (bits : Fin K → Bool) : Option Bool × ℕ :=
  runIndexed K bits 0 (Nat.zero_le K) a b hb hab

end Blotto.FixedWordCoin
