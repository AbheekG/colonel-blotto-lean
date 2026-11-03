import Blotto.BinaryRulerPrecision
import Blotto.BinaryPositiveWordReadWork

/-! Accuracy reading retains the reached positive Boolean words and one ruler
precision. Exact old accuracy words/suffix/precision and every rejection scope
are preserved. Unary word visits and ruler/comparison/shift visits derive a
linear incoming-length price. Small scalar/backend/controller/physical and
whole execution/space contracts remain separate. -/

namespace Blotto.BinaryAccuracyRulerReadWork

structure Prepared where
  words : BinaryAccuracyWords
  precision : ℕ
  correct : precision = words.precision

def prepare (words : BinaryAccuracyWords) : Prepared × ℕ :=
  let aligned := words.denominator.shifted 5
  let selected := BinaryRulerPrecision.precisionWithWork aligned words.numerator
  (⟨words,selected.1,BinaryRulerPrecision.precisionWithWork_state aligned words.numerator⟩,
    2 * (words.denominator.width + 5) + selected.2)

theorem prepare_words (words : BinaryAccuracyWords) : (prepare words).1.words = words := rfl

theorem prepare_precision (words : BinaryAccuracyWords) : (prepare words).1.precision = words.precision := (prepare words).1.correct

theorem prepare_bound (words : BinaryAccuracyWords) : (prepare words).2 ≤ 10 * (words.numerator.width + words.denominator.width + 6) := by
  have hp := BinaryRulerPrecision.precisionWithWork_bound (words.denominator.shifted 5) words.numerator
  rw [PositiveBinaryWord.width_shifted] at hp
  unfold prepare
  dsimp only
  omega

theorem Prepared.precision_bound (prepared : Prepared) : prepared.precision ≤ prepared.words.denominator.width + 5 := by
  have h := BinaryRulerPrecision.prepare_length_bound (prepared.words.denominator.shifted 5) prepared.words.numerator
  rw [BinaryRulerPrecision.prepare_length,PositiveBinaryWord.width_shifted] at h
  change prepared.words.precision ≤ prepared.words.denominator.width + 5 at h
  rw [← prepared.correct] at h
  exact h

def read (frame : List Bool) : Option (Prepared × List Bool) × ℕ :=
  let first := BinaryPositiveWordReadWork.read frame
  match first.1 with
  | none => (none,first.2)
  | some numerator =>
      let second := BinaryPositiveWordReadWork.read numerator.2
      match second.1 with
      | none => (none,first.2 + second.2)
      | some denominator =>
          let prepared := prepare ⟨numerator.1,denominator.1⟩
          (some (prepared.1,denominator.2),first.2 + second.2 + prepared.2)

def forget (parsed : Prepared × List Bool) : BinaryAccuracyWords × List Bool := (parsed.1.words,parsed.2)

theorem read_state (frame : List Bool) : (read frame).1.map forget = BinaryAccuracyWords.read frame := by
  unfold read BinaryAccuracyWords.read
  dsimp only
  rw [← BinaryPositiveWordReadWork.read_state frame]
  cases hn : (BinaryPositiveWordReadWork.read frame).1 with
  | none => rfl
  | some numerator =>
      dsimp only [Option.bind_some]
      rw [← BinaryPositiveWordReadWork.read_state numerator.2]
      cases hd : (BinaryPositiveWordReadWork.read numerator.2).1 with
      | none => rfl
      | some denominator => rfl

def bound (length : ℕ) : ℕ := 14 * (length + 5)

theorem bound_mono {a b : ℕ} (h : a ≤ b) : bound a ≤ bound b := Nat.mul_le_mul_left 14 (Nat.add_le_add_right h 5)

theorem read_bound (frame : List Bool) : (read frame).2 ≤ bound frame.length := by
  have hFirst := BinaryPositiveWordReadWork.read_bound frame
  unfold read
  dsimp only
  split
  · unfold bound
    exact hFirst.trans (by omega)
  · rename_i numerator hn
    have hN := BinaryPositiveWordReadWork.read_consumed frame numerator hn
    have hSecond := BinaryPositiveWordReadWork.read_bound numerator.2
    split
    · change (BinaryPositiveWordReadWork.read frame).2 + (BinaryPositiveWordReadWork.read numerator.2).2 ≤ _
      unfold bound
      omega
    · rename_i denominator hd
      have hD := BinaryPositiveWordReadWork.read_consumed numerator.2 denominator hd
      have hP := prepare_bound (⟨numerator.1,denominator.1⟩ : BinaryAccuracyWords)
      change (prepare ⟨numerator.1,denominator.1⟩).2 ≤ 10 * (numerator.1.width + denominator.1.width + 6) at hP
      change (BinaryPositiveWordReadWork.read frame).2 + (BinaryPositiveWordReadWork.read numerator.2).2 +
        (prepare ⟨numerator.1,denominator.1⟩).2 ≤ _
      unfold bound
      omega

theorem read_widths (frame : List Bool) (parsed : Prepared × List Bool) (h : (read frame).1 = some parsed) :
    2 * (parsed.1.words.numerator.width + parsed.1.words.denominator.width) + parsed.2.length + 2 ≤ frame.length := by
  have hs := read_state frame
  rw [h,Option.map_some] at hs
  exact BinaryAccuracyWords.read_width_bound frame parsed.2 parsed.1.words hs.symm

theorem read_suffix_length (frame : List Bool) (parsed : Prepared × List Bool) (h : (read frame).1 = some parsed) :
    parsed.2.length ≤ frame.length := by
  have hw := read_widths frame parsed h
  omega

theorem read_precision_bound (frame : List Bool) (parsed : Prepared × List Bool) (h : (read frame).1 = some parsed) :
    parsed.1.precision ≤ frame.length + 5 := by
  have hw := read_widths frame parsed h
  have hp := parsed.1.precision_bound
  omega

end Blotto.BinaryAccuracyRulerReadWork
