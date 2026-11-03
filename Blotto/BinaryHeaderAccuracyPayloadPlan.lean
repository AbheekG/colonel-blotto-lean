import Blotto.BinaryReversedPayloadPlan
import Blotto.BinaryAccuracyMeasured
import Blotto.BinaryStoredDimensionHeaderMeasured

/-! Dimension and positive accuracy payloads consume actual final-depth plans.
Old complete records/source charges are exact; only reached payload emission
is added. Header/control/precision/preparation/native scopes remain explicit. -/
namespace Blotto.BinaryHeaderAccuracyPayloadPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def header (frame : List Bool) : ((Option (BinaryStoredDimensionHeader.Header × List Bool) × Trace) × ℕ) × ℕ :=
  let produced := BinaryUnaryPayloadPlan.readWithEmission frame
  let raw := produced.1
  match raw.1.1 with
  | none => (((none,wrap 16 2 [raw.1.2]),raw.2+4),produced.2)
  | some parsed =>
      let prepared := BinaryStoredDimensionHeaderMeasured.prepare parsed.1
      (((some (prepared.1.1,parsed.2),wrap 24 2 [raw.1.2,prepared.1.2]),raw.2+prepared.2+8),produced.2)

theorem header_compat (frame : List Bool) : (header frame).1 = BinaryStoredDimensionHeaderMeasured.read frame := by
  simp only [header,BinaryStoredDimensionHeaderMeasured.read,BinaryUnaryPayloadPlan.read_compat]
  cases hRead : (BinaryUnaryPayloadMeasured.read frame).1.1 <;> simp only [hRead]

theorem header_price (frame : List Bool) : (header frame).2 ≤ 30*(header frame).1.2 := by
  have h := BinaryUnaryPayloadPlan.read_price frame
  unfold header
  dsimp only
  split <;> dsimp only <;> omega

def positive (frame : List Bool) : ((Option (PositiveBinaryWord × List Bool) × Trace) × ℕ) × ℕ :=
  let produced := BinaryReversedPayloadPlan.read frame
  let raw := produced.1
  match raw.1.1 with
  | none => (((none,wrap 16 2 [raw.1.2]),raw.2+4),produced.2)
  | some parsed =>
      let word := BinaryPositiveWordMeasured.parse parsed.1
      (((word.1.1.map (fun value => (value,parsed.2)),wrap 24 2 [raw.1.2,word.1.2]),raw.2+word.2+8),produced.2)

theorem positive_compat (frame : List Bool) : (positive frame).1 = BinaryPositiveWordMeasured.read frame := by
  simp only [positive,BinaryPositiveWordMeasured.read,BinaryReversedPayloadPlan.read_compat]
  cases hRead : (BinaryUnaryPayloadMeasured.readReversed frame).1.1 <;> simp only [hRead]

theorem positive_price (frame : List Bool) : (positive frame).2 ≤ 30*(positive frame).1.2 := by
  have h := BinaryReversedPayloadPlan.read_price frame
  unfold positive
  dsimp only
  split <;> dsimp only <;> omega

def accuracy (frame : List Bool) : ((Option (BinaryAccuracyRulerReadWork.Prepared × List Bool) × Trace) × ℕ) × ℕ :=
  let firstProduced := positive frame
  let first := firstProduced.1
  match first.1.1 with
  | none => (((none,wrap 16 2 [first.1.2]),first.2+4),firstProduced.2)
  | some numerator =>
      let secondProduced := positive numerator.2
      let second := secondProduced.1
      match second.1.1 with
      | none => (((none,wrap 24 2 [first.1.2,second.1.2]),first.2+second.2+8),firstProduced.2+secondProduced.2)
      | some denominator =>
          let prepared := BinaryAccuracyMeasured.prepare ⟨numerator.1,denominator.1⟩
          (((some (prepared.1.1,denominator.2),wrap 48 2 [first.1.2,second.1.2,prepared.1.2]),
            first.2+second.2+prepared.2+12),firstProduced.2+secondProduced.2)

theorem accuracy_compat (frame : List Bool) : (accuracy frame).1 = BinaryAccuracyMeasured.read frame := by
  simp only [accuracy,BinaryAccuracyMeasured.read,positive_compat]
  cases hf : (BinaryPositiveWordMeasured.read frame).1.1 with
  | none => simp only [hf]
  | some numerator =>
      simp only [hf]
      cases hs : (BinaryPositiveWordMeasured.read numerator.2).1.1 <;> simp only [hs]

theorem accuracy_price (frame : List Bool) : (accuracy frame).2 ≤ 30*(accuracy frame).1.2 := by
  have hf := positive_price frame
  unfold accuracy
  dsimp only
  split
  · dsimp only; omega
  · rename_i numerator hFirst
    have hs := positive_price numerator.2
    split <;> dsimp only <;> omega

end Blotto.BinaryHeaderAccuracyPayloadPlan
