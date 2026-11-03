import Blotto.BinaryHeaderControlPlan
import Blotto.BinaryRequestRulerPlan

/-! Concrete dimension/positive readers consume planned header control once.
Accuracy retains both prior payload/ruler prices and forwards the new reached
control emission. Complete previous records remain exact on every path. -/
namespace Blotto.BinaryHeaderControlReaders
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 4000000

def header (frame : List Bool) : (((Option (BinaryStoredDimensionHeader.Header × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  let produced := BinaryUnaryPayloadPlan.readWithEmission frame
  let raw := produced.1
  match raw.1.1 with
  | none => ((((none,wrap 16 2 [raw.1.2]),raw.2+4),produced.2),0)
  | some parsed =>
      let preparedProduced := BinaryHeaderControlPlan.prepare parsed.1
      let prepared := preparedProduced.1
      ((((some (prepared.1.1,parsed.2),wrap 24 2 [raw.1.2,prepared.1.2]),raw.2+prepared.2+8),produced.2),preparedProduced.2)

theorem header_compat (frame : List Bool) : (header frame).1 = BinaryHeaderAccuracyPayloadPlan.header frame := by
  simp only [header,BinaryHeaderAccuracyPayloadPlan.header,BinaryHeaderControlPlan.prepare_compat]
  cases h : (BinaryUnaryPayloadPlan.readWithEmission frame).1.1.1 <;> simp only [h]

theorem header_price (frame : List Bool) : (header frame).2 ≤ 30*(header frame).1.1.2 := by
  unfold header
  dsimp only
  split
  · dsimp only; omega
  · rename_i parsed hs
    have hp := BinaryHeaderControlPlan.prepare_price parsed.1
    dsimp only
    omega

def positive (frame : List Bool) : (((Option (PositiveBinaryWord × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  let produced := BinaryReversedPayloadPlan.read frame
  let raw := produced.1
  match raw.1.1 with
  | none => ((((none,wrap 16 2 [raw.1.2]),raw.2+4),produced.2),0)
  | some parsed =>
      let wordProduced := BinaryHeaderControlPlan.positive parsed.1
      let word := wordProduced.1
      ((((word.1.1.map (fun value => (value,parsed.2)),wrap 24 2 [raw.1.2,word.1.2]),raw.2+word.2+8),produced.2),wordProduced.2)

theorem positive_compat (frame : List Bool) : (positive frame).1 = BinaryHeaderAccuracyPayloadPlan.positive frame := by
  simp only [positive,BinaryHeaderAccuracyPayloadPlan.positive,BinaryHeaderControlPlan.positive_compat]
  cases h : (BinaryReversedPayloadPlan.read frame).1.1.1 <;> simp only [h]

theorem positive_price (frame : List Bool) : (positive frame).2 ≤ 30*(positive frame).1.1.2 := by
  unfold positive
  dsimp only
  split
  · dsimp only; omega
  · rename_i parsed hs
    have hp := BinaryHeaderControlPlan.positive_price parsed.1
    dsimp only
    omega

def accuracy (frame : List Bool) :
    (((Option (BinaryAccuracyRulerReadWork.Prepared × List Bool) × Trace) × ℕ) × (ℕ × ℕ)) × ℕ :=
  let firstProduced := positive frame
  let first := firstProduced.1.1
  match first.1.1 with
  | none => ((((none,wrap 16 2 [first.1.2]),first.2+4),(firstProduced.1.2,0)),firstProduced.2)
  | some numerator =>
      let secondProduced := positive numerator.2
      let second := secondProduced.1.1
      match second.1.1 with
      | none => ((((none,wrap 24 2 [first.1.2,second.1.2]),first.2+second.2+8),
          (firstProduced.1.2+secondProduced.1.2,0)),firstProduced.2+secondProduced.2)
      | some denominator =>
          let produced := BinaryRequestRulerPlan.accuracyPrepare ⟨numerator.1,denominator.1⟩
          let prepared := produced.1
          ((((some (prepared.1.1,denominator.2),wrap 48 2 [first.1.2,second.1.2,prepared.1.2]),
            first.2+second.2+prepared.2+12),(firstProduced.1.2+secondProduced.1.2,produced.2)),firstProduced.2+secondProduced.2)

theorem accuracy_compat (frame : List Bool) : (accuracy frame).1 = BinaryRequestRulerPlan.accuracyRead frame := by
  simp only [accuracy,BinaryRequestRulerPlan.accuracyRead,positive_compat]
  cases hf : (BinaryHeaderAccuracyPayloadPlan.positive frame).1.1.1 with
  | none => simp only [hf]
  | some numerator =>
      simp only [hf]
      cases hs : (BinaryHeaderAccuracyPayloadPlan.positive numerator.2).1.1.1 <;> simp only [hs]

theorem accuracy_price (frame : List Bool) : (accuracy frame).2 ≤ 30*(accuracy frame).1.1.2 := by
  have hf := positive_price frame
  unfold accuracy
  dsimp only
  split
  · dsimp only; omega
  · rename_i numerator hn
    have hs := positive_price numerator.2
    split <;> dsimp only <;> omega

end Blotto.BinaryHeaderControlReaders
