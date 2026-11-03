import Blotto.BinaryPositiveWordMeasured
import Blotto.BinaryRulerPrecisionMeasured
import Blotto.BinaryAccuracyLifetime

/-! One measured accuracy reader executes both positive-word reads and the
actual ruler precision path, preserving all original words/precision/suffixes
and traces. Source charges include constant five-cell ruler construction.
Numeric payload decoding and an old second parser are not executed. -/
namespace Blotto.BinaryAccuracyMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def prepare (words : BinaryAccuracyWords) : (BinaryAccuracyRulerReadWork.Prepared × Trace) × ℕ :=
  let ruler := List.replicate 5 false
  let aligned := BinaryRulerPrecisionMeasured.shifted words.denominator ruler
  let selected := BinaryRulerPrecisionMeasured.precision aligned.1.1 words.numerator
  have hAligned : aligned.1.1 = words.denominator.shifted 5 := by
    rw [BinaryRulerPrecisionMeasured.shifted_erases,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,
      BinaryRulerPrecision.shifted_state]
    simp only [ruler,List.length_replicate]
  have hCorrect : selected.1.1 = words.precision := by
    rw [BinaryRulerPrecisionMeasured.precision_erases,
      BinaryRulerPrecisionLifetime.precisionWithTrace_state,hAligned]
    rfl
  ((⟨words,selected.1.1,hCorrect⟩,wrapList 5 32 2 [aligned.1.2,selected.1.2]),aligned.2+selected.2+32)

theorem prepare_erases (words : BinaryAccuracyWords) :
    (prepare words).1 = BinaryAccuracyLifetime.prepareWithTrace words := by
  simp only [prepare,BinaryAccuracyLifetime.prepareWithTrace,
    BinaryRulerPrecisionMeasured.shifted_erases,BinaryRulerPrecisionMeasured.precision_erases]

theorem prepare_work (words : BinaryAccuracyWords) :
    (prepare words).2 ≤ 1024*(words.numerator.width+words.denominator.width+8) := by
  have hs := BinaryRulerPrecisionMeasured.shifted_work words.denominator (List.replicate 5 false)
  have hp := BinaryRulerPrecisionMeasured.precision_work
    (BinaryRulerPrecisionMeasured.shifted words.denominator (List.replicate 5 false)).1.1 words.numerator
  rw [BinaryRulerPrecisionMeasured.shifted_width] at hp
  simp only [List.length_replicate] at hs hp
  change (BinaryRulerPrecisionMeasured.shifted words.denominator (List.replicate 5 false)).2+
    (BinaryRulerPrecisionMeasured.precision
      (BinaryRulerPrecisionMeasured.shifted words.denominator (List.replicate 5 false)).1.1 words.numerator).2+32 ≤ _
  omega

def read (frame : List Bool) : (Option (BinaryAccuracyRulerReadWork.Prepared × List Bool) × Trace) × ℕ :=
  let first := BinaryPositiveWordMeasured.read frame
  match first.1.1 with
  | none => ((none,wrap 16 2 [first.1.2]),first.2+4)
  | some numerator =>
      let second := BinaryPositiveWordMeasured.read numerator.2
      match second.1.1 with
      | none => ((none,wrap 24 2 [first.1.2,second.1.2]),first.2+second.2+8)
      | some denominator =>
          let prepared := prepare ⟨numerator.1,denominator.1⟩
          ((some (prepared.1.1,denominator.2),wrap 48 2 [first.1.2,second.1.2,prepared.1.2]),
            first.2+second.2+prepared.2+12)

theorem read_erases (frame : List Bool) : (read frame).1 = BinaryAccuracyLifetime.readWithTrace frame := by
  unfold read BinaryAccuracyLifetime.readWithTrace
  dsimp only
  simp only [BinaryPositiveWordMeasured.read_erases,prepare_erases]
  cases (BinaryPositiveWordLifetime.readWithTrace frame).1 with
  | none => rfl
  | some numerator =>
      dsimp only
      cases (BinaryPositiveWordLifetime.readWithTrace numerator.2).1 <;> rfl

def price (length : ℕ) : ℕ := 2048*(length+8)

theorem read_work (frame : List Bool) : (read frame).2 ≤ price frame.length := by
  have hFirst := BinaryPositiveWordMeasured.read_work frame
  unfold read
  dsimp only
  split
  · unfold price
    omega
  · rename_i numerator hn
    have hN := BinaryPositiveWordMeasured.read_consumed frame numerator hn
    have hSecond := BinaryPositiveWordMeasured.read_work numerator.2
    split
    · unfold price
      omega
    · rename_i denominator hd
      have hD := BinaryPositiveWordMeasured.read_consumed numerator.2 denominator hd
      have hp := prepare_work (⟨numerator.1,denominator.1⟩ : BinaryAccuracyWords)
      change (prepare ⟨numerator.1,denominator.1⟩).2 ≤ 1024*(numerator.1.width+denominator.1.width+8) at hp
      unfold price
      omega

theorem read_widths (frame : List Bool) (parsed : BinaryAccuracyRulerReadWork.Prepared × List Bool)
    (h : (read frame).1.1 = some parsed) :
    parsed.1.words.numerator.width+parsed.1.words.denominator.width ≤ frame.length := by
  have hw := BinaryAccuracyRulerReadWork.read_widths frame parsed
    ((BinaryAccuracyLifetime.readWithTrace_state frame).symm.trans
      ((congrArg Prod.fst (read_erases frame)).symm.trans h))
  omega

theorem read_precision_bound (frame : List Bool) (parsed : BinaryAccuracyRulerReadWork.Prepared × List Bool)
    (h : (read frame).1.1 = some parsed) : parsed.1.precision ≤ frame.length+5 :=
  BinaryAccuracyLifetime.read_precision_bound frame parsed ((congrArg Prod.fst (read_erases frame)).symm.trans h)

theorem read_suffix_length (frame : List Bool) (parsed : BinaryAccuracyRulerReadWork.Prepared × List Bool)
    (h : (read frame).1.1 = some parsed) : parsed.2.length ≤ frame.length :=
  BinaryAccuracyLifetime.read_suffix_length frame parsed ((congrArg Prod.fst (read_erases frame)).symm.trans h)

theorem read_usage (frame : List Bool) : usage (read frame).1.2 ≤ BinaryAccuracyLifetime.envelope frame.length := by
  rw [read_erases]
  exact BinaryAccuracyLifetime.readWithTrace_usage frame

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (read frame).1.2 steps ≤ borrowed+frame.length+BinaryAccuracyLifetime.envelope frame.length ∧
    framePeak ((read frame).1.2.take steps) ≤ BinaryAccuracyLifetime.envelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage frame) _ steps

end Blotto.BinaryAccuracyMeasured
