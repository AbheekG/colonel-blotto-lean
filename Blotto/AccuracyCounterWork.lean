import Blotto.CountedWidthWork
import Blotto.UnaryAccuracyTraversal

/-! Accuracy processing now includes explicit width-counter carries and
small final counter merges in its ledger. This still excludes internal decoder
index arithmetic, integer-backend, allocator and physical instruction costs. -/

namespace Blotto.BinaryAccuracyWords

def counterWork (a : BinaryAccuracyWords) : ℕ :=
  (a.denominator.shifted 5).ratioWidthCarryWork a.numerator +
    (a.denominator.shifted 5).ratioWidthMergeWork a.numerator

theorem counterWork_bound (a : BinaryAccuracyWords) : a.counterWork ≤ 30 * (a.numerator.width + a.denominator.width + 5) := by
  have hCarry := (a.denominator.shifted 5).ratioWidthCarryWork_bound a.numerator
  have hMerge := (a.denominator.shifted 5).ratioWidthMergeWork_bound a.numerator
  rw [PositiveBinaryWord.width_shifted] at hCarry hMerge
  unfold counterWork
  omega

def readWithCountersWork (frame : List Bool) : ℕ := unaryReadTraversalWork frame +
  match read frame with
  | none => 0
  | some (words, _) => words.counterWork

theorem readWithCountersWork_bound (frame : List Bool) : readWithCountersWork frame ≤ 22 * frame.length + 184 := by
  have hTraverse := unaryReadTraversalWork_bound frame
  unfold readWithCountersWork
  cases h : read frame with
  | none => dsimp only; omega
  | some pair =>
    rcases pair with ⟨words, suffix⟩
    have hWidth := read_width_bound frame suffix words h
    have hCounter := words.counterWork_bound
    change unaryReadTraversalWork frame + words.counterWork ≤ 22 * frame.length + 184
    omega

end Blotto.BinaryAccuracyWords
