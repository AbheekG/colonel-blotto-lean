import Blotto.BinaryRulerPrecisionLifetime
import Blotto.BinaryAccuracyRulerReadWork

/-! Actual positive-word parsing and one retained Boolean-ruler precision.
Both old accuracy words, selected precision and suffix/rejection are exact.
Source widths and incoming frame length derive every retained reservation. -/
namespace Blotto.BinaryAccuracyLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def prepareWithTrace (words : BinaryAccuracyWords) : BinaryAccuracyRulerReadWork.Prepared × Trace :=
  let ruler := List.replicate 5 false
  let aligned := BinaryRulerPrecisionLifetime.shiftedWithTrace words.denominator ruler
  let selected := BinaryRulerPrecisionLifetime.precisionWithTrace aligned.1 words.numerator
  have hAligned : aligned.1 = words.denominator.shifted 5 := by
    rw [BinaryRulerPrecisionLifetime.shiftedWithTrace_state,BinaryRulerPrecision.shifted_state]
    simp only [ruler,List.length_replicate]
  have hCorrect : selected.1 = words.precision := by
    rw [BinaryRulerPrecisionLifetime.precisionWithTrace_state,hAligned]
    rfl
  (⟨words,selected.1,hCorrect⟩,wrapList 5 32 2 [aligned.2,selected.2])

theorem prepareWithTrace_state (words : BinaryAccuracyWords) :
    (prepareWithTrace words).1 = (BinaryAccuracyRulerReadWork.prepare words).1 := by
  unfold prepareWithTrace BinaryAccuracyRulerReadWork.prepare
  dsimp only
  simp only [BinaryRulerPrecisionLifetime.precisionWithTrace_state,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,
    BinaryRulerPrecision.shifted_state,List.length_replicate,BinaryRulerPrecision.precisionWithWork_state]

theorem prepareWithTrace_usage (words : BinaryAccuracyWords) :
    usage (prepareWithTrace words).2 ≤ 1024*(words.numerator.width+words.denominator.width+8) := by
  let ruler := List.replicate 5 false
  let aligned := BinaryRulerPrecisionLifetime.shiftedWithTrace words.denominator ruler
  have hShift := BinaryRulerPrecisionLifetime.shiftedWithTrace_usage words.denominator ruler
  have hSelected := BinaryRulerPrecisionLifetime.precisionWithTrace_usage aligned.1 words.numerator
  have hWidth : aligned.1.width = words.denominator.width+5 := by
    dsimp only [aligned]
    rw [BinaryRulerPrecisionLifetime.shiftedWithTrace_state,BinaryRulerPrecision.shifted_state,PositiveBinaryWord.width_shifted]
    simp only [ruler,List.length_replicate]
  rw [hWidth] at hSelected
  simp only [ruler,List.length_replicate] at hShift
  have hw := wrapList_usage 5 32 2 [aligned.2,(BinaryRulerPrecisionLifetime.precisionWithTrace aligned.1 words.numerator).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (prepareWithTrace words).2 ≤ _ at hw
  change usage aligned.2 ≤ _ at hShift
  omega

def readWithTrace (frame : List Bool) : Option (BinaryAccuracyRulerReadWork.Prepared × List Bool) × Trace :=
  let first := BinaryPositiveWordLifetime.readWithTrace frame
  match first.1 with
  | none => (none,wrap 16 2 [first.2])
  | some numerator =>
      let second := BinaryPositiveWordLifetime.readWithTrace numerator.2
      match second.1 with
      | none => (none,wrap 24 2 [first.2,second.2])
      | some denominator =>
          let prepared := prepareWithTrace ⟨numerator.1,denominator.1⟩
          (some (prepared.1,denominator.2),wrap 48 2 [first.2,second.2,prepared.2])

theorem readWithTrace_state (frame : List Bool) : (readWithTrace frame).1 = (BinaryAccuracyRulerReadWork.read frame).1 := by
  unfold readWithTrace BinaryAccuracyRulerReadWork.read
  dsimp only
  rw [BinaryPositiveWordLifetime.readWithTrace_state,BinaryPositiveWordReadWork.read_state]
  cases PositiveBinaryWord.read frame with
  | none => rfl
  | some numerator =>
      dsimp only
      rw [BinaryPositiveWordLifetime.readWithTrace_state,BinaryPositiveWordReadWork.read_state]
      cases PositiveBinaryWord.read numerator.2 with
      | none => rfl
      | some denominator => simp only [prepareWithTrace_state]

def envelope (length : ℕ) : ℕ := 2048*(length+8)

theorem envelope_mono {a b : ℕ} (h : a ≤ b) : envelope a ≤ envelope b := by unfold envelope; omega

theorem readWithTrace_usage (frame : List Bool) : usage (readWithTrace frame).2 ≤ envelope frame.length := by
  have hFirst := BinaryPositiveWordLifetime.readWithTrace_usage frame
  unfold readWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryPositiveWordLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryPositiveWordLifetime.readWithTrace frame).2]) ≤ _
    unfold envelope
    omega
  · rename_i numerator hn
    have hN := BinaryPositiveWordLifetime.read_consumed frame numerator hn
    have hSecond := BinaryPositiveWordLifetime.readWithTrace_usage numerator.2
    split
    · have hw := wrap_usage 24 2 [(BinaryPositiveWordLifetime.readWithTrace frame).2,
        (BinaryPositiveWordLifetime.readWithTrace numerator.2).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [(BinaryPositiveWordLifetime.readWithTrace frame).2,
        (BinaryPositiveWordLifetime.readWithTrace numerator.2).2]) ≤ _
      unfold envelope
      omega
    · rename_i denominator hd
      have hD := BinaryPositiveWordLifetime.read_consumed numerator.2 denominator hd
      have hPrepare := prepareWithTrace_usage (⟨numerator.1,denominator.1⟩ : BinaryAccuracyWords)
      change usage (prepareWithTrace ⟨numerator.1,denominator.1⟩).2 ≤ 1024*(numerator.1.width+denominator.1.width+8) at hPrepare
      have hw := wrap_usage 48 2 [(BinaryPositiveWordLifetime.readWithTrace frame).2,
        (BinaryPositiveWordLifetime.readWithTrace numerator.2).2,(prepareWithTrace ⟨numerator.1,denominator.1⟩).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 48 2 [(BinaryPositiveWordLifetime.readWithTrace frame).2,
        (BinaryPositiveWordLifetime.readWithTrace numerator.2).2,(prepareWithTrace ⟨numerator.1,denominator.1⟩).2]) ≤ _
      unfold envelope
      omega

theorem read_suffix_length (frame : List Bool) (parsed : BinaryAccuracyRulerReadWork.Prepared × List Bool)
    (h : (readWithTrace frame).1 = some parsed) : parsed.2.length ≤ frame.length :=
  BinaryAccuracyRulerReadWork.read_suffix_length frame parsed ((readWithTrace_state frame).symm.trans h)

theorem read_precision_bound (frame : List Bool) (parsed : BinaryAccuracyRulerReadWork.Prepared × List Bool)
    (h : (readWithTrace frame).1 = some parsed) : parsed.1.precision ≤ frame.length+5 :=
  BinaryAccuracyRulerReadWork.read_precision_bound frame parsed ((readWithTrace_state frame).symm.trans h)

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (readWithTrace frame).2 steps ≤ borrowed+frame.length+envelope frame.length ∧
    framePeak ((readWithTrace frame).2.take steps) ≤ envelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage frame) _ steps

end Blotto.BinaryAccuracyLifetime
