import Blotto.BinaryWordPrecision
import Blotto.BinaryAccuracyFrame

/-! Accuracy words are read and compared as Boolean strings. Neither accuracy
payload is assembled as an integer. Width counters use Boolean carries and
balanced assembly of their final small values; payload values are proof bridges. -/

namespace Blotto

structure BinaryAccuracyWords where
  numerator : PositiveBinaryWord
  denominator : PositiveBinaryWord

theorem BinaryAccuracyInput.eq_of_words (a b : BinaryAccuracyInput)
    (hN : a.numerator = b.numerator) (hD : a.denominator = b.denominator) : a = b := by
  cases a
  cases b
  cases hN
  cases hD
  rfl

namespace BinaryAccuracyWords

def numeric (a : BinaryAccuracyWords) : BinaryAccuracyInput :=
  ⟨a.numerator.value, a.denominator.value, a.numerator.value_pos, a.denominator.value_pos⟩

def precision (a : BinaryAccuracyWords) : ℕ := (a.denominator.shifted 5).ratioPrecision a.numerator

def read (frame : List Bool) : Option (BinaryAccuracyWords × List Bool) :=
  (PositiveBinaryWord.read frame).bind (fun first =>
    (PositiveBinaryWord.read first.2).map (fun second => (⟨first.1, second.1⟩, second.2)))

theorem precision_eq (a : BinaryAccuracyWords) : a.precision = a.numeric.precision := by
  rw [precision, PositiveBinaryWord.ratioPrecision_eq, PositiveBinaryWord.value_shifted]
  simp [numeric, BinaryAccuracyInput.precision, Nat.shiftLeft_eq, Nat.mul_comm]

theorem read_encode_append (a : BinaryAccuracyInput) (suffix : List Bool) :
    ∃ w, read (BinaryAccuracyFrame.encode a ++ suffix) = some (w, suffix) ∧ w.numeric = a := by
  rcases PositiveBinaryWord.read_encode_append a.numerator a.numerator_pos (BinaryNatFrame.encode a.denominator ++ suffix) with
    ⟨num, hNum, hN⟩
  rcases PositiveBinaryWord.read_encode_append a.denominator a.denominator_pos suffix with ⟨den, hDen, hD⟩
  refine ⟨⟨num, den⟩, ?_, ?_⟩
  · simp only [read, BinaryAccuracyFrame.encode, List.append_assoc, hNum, Option.bind_some, hDen, Option.map_some]
  · unfold numeric
    exact BinaryAccuracyInput.eq_of_words _ a hN hD

def traversalWork (a : BinaryAccuracyWords) : ℕ :=
  a.denominator.width + 5 + (a.denominator.shifted 5).ratioTraversalWork a.numerator

theorem traversalWork_bound (a : BinaryAccuracyWords) :
    a.traversalWork ≤ 6 * (a.numerator.width + a.denominator.width + 5) := by
  have h := PositiveBinaryWord.ratioTraversalWork_bound (a.denominator.shifted 5) a.numerator
  rw [PositiveBinaryWord.width_shifted] at h
  unfold traversalWork
  omega

theorem traversalWork_encoded_bound (a : BinaryAccuracyInput) (w : BinaryAccuracyWords) (h : w.numeric = a) :
    w.traversalWork ≤ 3 * (BinaryAccuracyFrame.encode a).length + 24 := by
  have hn : w.numerator.value = a.numerator := congrArg BinaryAccuracyInput.numerator h
  have hd : w.denominator.value = a.denominator := congrArg BinaryAccuracyInput.denominator h
  have ht := w.traversalWork_bound
  rw [w.numerator.width_eq, w.denominator.width_eq, hn, hd] at ht
  rw [BinaryAccuracyFrame.encode_length]
  omega

end BinaryAccuracyWords
end Blotto
