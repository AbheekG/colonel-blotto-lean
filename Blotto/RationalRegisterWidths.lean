import Blotto.RationalArithmeticProgram
import Blotto.RationalExpressionWordWidth

/-! Append-only arithmetic registers retain all earlier values. Bounds for
the final register array therefore certify every intermediate array, including
the zero returned by a total out-of-range read. -/

namespace Blotto.RationalArithmeticProgram

def WordBounds (registers : Array ℚ) (W : ℕ) : Prop :=
  ∀ j, rationalWordWidth (registers.getD j 0) ≤ W

theorem execute_preserves (instruction : RealArithmeticInstruction) (registers : Array ℚ)
    (j : ℕ) (hj : j < registers.size) :
    (instruction.executeRat registers).getD j 0 = registers.getD j 0 := by
  simp only [RealArithmeticInstruction.executeRat, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hj,
    getElem?_pos registers j hj, Option.getD_some]

theorem run_preserves (program : List RealArithmeticInstruction) (registers : Array ℚ)
    (j : ℕ) (hj : j < registers.size) : (run program registers).getD j 0 = registers.getD j 0 := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih =>
    rw [run, ih _ (by rw [instruction.executeRat_size]; omega), execute_preserves instruction registers j hj]

theorem WordBounds.before_run {program : List RealArithmeticInstruction} {registers : Array ℚ} {W : ℕ}
    (h : WordBounds (run program registers) W) (hZero : rationalWordWidth (0 : ℚ) ≤ W) :
    WordBounds registers W := by
  intro j
  by_cases hj : j < registers.size
  · rw [← run_preserves program registers j hj]
    exact h j
  · simpa only [Array.getD_eq_getD_getElem?, getElem?_neg registers j hj, Option.getD_none] using hZero

theorem WordBounds.prefix {program : List RealArithmeticInstruction} {registers : Array ℚ} {W : ℕ}
    (h : WordBounds (run program registers) W) (hZero : rationalWordWidth (0 : ℚ) ≤ W) (k : ℕ) :
    WordBounds (run (program.take k) registers) W := by
  have hFull : WordBounds (run (program.drop k) (run (program.take k) registers)) W := by
    rw [← run_append, List.take_append_drop]
    exact h
  exact hFull.before_run hZero

end Blotto.RationalArithmeticProgram
