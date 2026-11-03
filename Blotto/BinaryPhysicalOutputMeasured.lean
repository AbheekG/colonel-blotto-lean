import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryWordObjectArrayMeasured
import Blotto.BinaryWordObjectArrayAccessMeasured
import Blotto.BooleanArrayIndexMeasured
import Blotto.BinaryTapeFrameMeasured
import Blotto.BinaryPhysicalOutputWork

/-! One selected physical-output execution returns its bytes, preceding full
source trace and preceding full source-work charge. The actual prepared store,
Boolean indices, heap reads, quadratic results and framed bytes are consumed
directly. Trace/price observer evaluation and native machine realization are
separate from this joined Boolean/list source contract. -/

namespace Blotto.BinaryPhysicalOutputMeasured
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryWordObjectArray
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 4000000

def emitWithExtras {n : ℕ} (store : Store n) (budget : SignedWord) : List (List Bool) → ((Option (List Bool) × Trace) × ℕ) × ℕ
  | [] => (((some [],wrap 16 1 []),4),0)
  | index::indices =>
      let read := BinaryWordObjectArrayAccessMeasured.get store index
      match read.1.1 with
      | none => (((none,wrap 24 2 [read.1.2]),read.2+8),0)
      | some word =>
          let scaled := BinaryNormalizedCoordinate.opcode .mul budget word
          let framed := BinaryTapeFrameMeasured.word scaled.1.1.1
          let produced := emitWithExtras store budget indices
          let later := produced.1
          let extras := scaled.2+produced.2
          match later.1.1 with
          | none => (((none,wrap 64 2 [read.1.2,scaled.1.1.2,framed.1.2,later.1.2]),
              read.2+scaled.1.2+framed.2+later.2+16),extras)
          | some bytes =>
              let joined := BinaryHeapTapeMeasured.append framed.1.1 bytes
              (((some joined.1.1,wrap 64 2 [read.1.2,scaled.1.1.2,framed.1.2,later.1.2,joined.1.2]),
                read.2+scaled.1.2+framed.2+later.2+joined.2.work+16),extras)

def emit {n : ℕ} (store : Store n) (budget : SignedWord) : List (List Bool) → (Option (List Bool) × Trace) × ℕ :=
  fun indices => (emitWithExtras store budget indices).1

theorem emitWithExtras_compat {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) :
    (emitWithExtras store budget indices).1 = emit store budget indices := rfl

theorem emit_nil {n : ℕ} (store : Store n) (budget : SignedWord) : emit store budget [] = ((some [],wrap 16 1 []),4) := rfl

theorem emit_cons {n : ℕ} (store : Store n) (budget : SignedWord) (index : List Bool) (indices : List (List Bool)) :
    emit store budget (index::indices) =
      let read := BinaryWordObjectArrayAccessMeasured.get store index
      match read.1.1 with
      | none => ((none,wrap 24 2 [read.1.2]),read.2+8)
      | some word =>
          let scaled := BinaryPlannedQuadratic.apply .mul budget word
          let framed := BinaryTapeFrameMeasured.word scaled.1.1
          let later := emit store budget indices
          match later.1.1 with
          | none => ((none,wrap 64 2 [read.1.2,scaled.1.2,framed.1.2,later.1.2]),
              read.2+scaled.2+framed.2+later.2+16)
          | some bytes =>
              let joined := BinaryHeapTapeMeasured.append framed.1.1 bytes
              ((some joined.1.1,wrap 64 2 [read.1.2,scaled.1.2,framed.1.2,later.1.2,joined.1.2]),
                read.2+scaled.2+framed.2+later.2+joined.2.work+16) := by
  simp only [emit,emitWithExtras,BinaryNormalizedCoordinate.opcode_record]
  cases hRead : (BinaryWordObjectArrayAccessMeasured.get store index).1.1 with
  | none => simp only [hRead]
  | some word =>
      simp only [hRead]
      cases hLater : (emitWithExtras store budget indices).1.1.1 <;> simp only [hLater]


theorem emit_erases {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) :
    (emit store budget indices).1 = BinaryPhysicalRowOutput.emitWithTrace store budget indices := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,emit_nil,emit_cons,BinaryPhysicalRowOutput.emitWithTrace,BinaryWordObjectArrayAccessMeasured.get_erases]
      cases hRead : (BinaryWordObjectArrayAccess.getWithTrace store index).1 with
      | none => simp only
      | some word =>
          simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryQuadraticMeasured.apply_erases,BinaryTapeFrameMeasured.word_erases,ih]
          cases hLater : (BinaryPhysicalRowOutput.emitWithTrace store budget indices).1 with
          | none => simp only
          | some bytes => simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryHeapTapeMeasured.append_erases]

theorem emit_data {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) :
    (emit store budget indices).1.1 = (BinaryPhysicalOutputWork.emitWithWork store budget indices).1 := by
  rw [emit_erases,BinaryPhysicalOutputWork.emit_state]

theorem emit_work {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) :
    (emit store budget indices).2 = (BinaryPhysicalOutputWork.emitWithWork store budget indices).2 := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,emit_nil,emit_cons,BinaryPhysicalOutputWork.emitWithWork,BinaryWordObjectArrayAccessMeasured.get_data,
        BinaryWordObjectArrayAccessMeasured.get_work]
      cases hRead : (getWithWork store index).1 with
      | none => simp only
      | some word =>
          simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryQuadraticMeasured.apply_data,BinaryQuadraticMeasured.apply_work,
            BinaryTapeFrameMeasured.word_data,BinaryTapeFrameMeasured.word_work,emit_data,ih]
          cases hLater : (BinaryPhysicalOutputWork.emitWithWork store budget indices).1 with
          | none => simp only
          | some bytes => simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryHeapTapeMeasured.append_charge]

theorem prepared_data (words : List SignedWord) :
    (BinaryWordObjectArrayMeasured.prepare words).1.1 =
      (BinaryWordObjectArrayLifetime.prepareWithWork words).1 := by
  rw [BinaryWordObjectArrayMeasured.prepare_state,BinaryWordObjectArrayLifetime.prepareWithWork_state]

theorem indices_data (words : List SignedWord) :
    (BooleanArrayIndexMeasured.enumerate words).1.1 = (BooleanArrayIndexWork.enumerateWithWork words).1 := by
  rw [BooleanArrayIndexMeasured.enumerate_erases,BooleanArrayIndexWork.enumerate_state]

theorem append_work (first second : List Bool) :
    (BinaryHeapTapeMeasured.append first second).2.work = 4*first.length+1 :=
  (BinaryHeapTapeMeasured.append_price first second).1

theorem append_reference_work (first second : List Bool) :
    (BinaryPRGWordStoreHeapMachine.appendWithWork first second).2.work = 4*first.length+1 :=
  (BinaryPRGWordStoreHeapMachine.appendWithWork_price first second).1

set_option cleanup.letToHave false in
def outputWithExtras (budget : SignedWord) (header : List Bool) (words : List SignedWord) : ((List Bool × Trace) × ℕ) × ℕ :=
  let prepared := BinaryWordObjectArrayMeasured.prepare words
  let indices := BooleanArrayIndexMeasured.enumerate words
  let produced := emitWithExtras prepared.1.1 budget indices.1.1
  let emitted := produced.1
  have hSome : emitted.1.1.isSome := by
    change (emit prepared.1.1 budget indices.1.1).1.1.isSome
    rw [emit_erases,BinaryWordObjectArrayMeasured.prepare_state,BooleanArrayIndexMeasured.enumerate_erases,
      BinaryPhysicalRowOutput.emit_enumerate _ words (prepare_realizes words) budget]
    rfl
  let joined := BinaryHeapTapeMeasured.append header (emitted.1.1.get hSome)
  (((joined.1.1,wrap 64 2 [prepared.1.2,indices.1.2,emitted.1.2,joined.1.2]),
    prepared.2+indices.2+emitted.2+joined.2.work+16),produced.2)

def output (budget : SignedWord) (header : List Bool) (words : List SignedWord) : (List Bool × Trace) × ℕ :=
  (outputWithExtras budget header words).1

theorem outputWithExtras_compat (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    (outputWithExtras budget header words).1 = output budget header words := rfl

theorem output_record (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    output budget header words =
  let prepared := BinaryWordObjectArrayMeasured.prepare words
  let indices := BooleanArrayIndexMeasured.enumerate words
  let emitted := emit prepared.1.1 budget indices.1.1
  have hSome : emitted.1.1.isSome := by
    rw [emit_erases,BinaryWordObjectArrayMeasured.prepare_state,BooleanArrayIndexMeasured.enumerate_erases,
      BinaryPhysicalRowOutput.emit_enumerate _ words (prepare_realizes words) budget]
    rfl
  let joined := BinaryHeapTapeMeasured.append header (emitted.1.1.get hSome)
  ((joined.1.1,wrap 64 2 [prepared.1.2,indices.1.2,emitted.1.2,joined.1.2]),
    prepared.2+indices.2+emitted.2+joined.2.work+16) := by
  simp only [output,outputWithExtras,emitWithExtras_compat]


theorem output_erases (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    (output budget header words).1 = BinaryPhysicalOutputLifetime.outputWithTrace budget header words := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,output_record,BinaryPhysicalOutputLifetime.outputWithTrace,BinaryWordObjectArrayMeasured.prepare_erases,
    BooleanArrayIndexMeasured.enumerate_erases,emit_erases,BinaryHeapTapeMeasured.append_erases]

theorem output_data (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    (output budget header words).1.1 = (BinaryPhysicalOutputWork.outputWithWork budget header words).1 := by
  rw [output_erases,BinaryPhysicalOutputWork.output_state]

theorem output_work (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    (output budget header words).2 = (BinaryPhysicalOutputWork.outputWithWork budget header words).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,output_record,BinaryPhysicalOutputWork.outputWithWork,append_work,append_reference_work,
    BinaryWordObjectArrayMeasured.prepare_work,BooleanArrayIndexMeasured.enumerate_work,
    emit_work,prepared_data,indices_data]

theorem output_bound (budget : SignedWord) (header : List Bool) (words : List SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (W : ℕ) (hB : width budget ≤ W)
    (hWords : ∀ word ∈ words,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (output budget header words).2 ≤ BinaryPhysicalOutputLifetime.bound words.length W header.length := by
  rw [output_work]
  exact BinaryPhysicalOutputWork.output_work budget header words hBV W hB hWords

theorem output_all_prefix (budget : SignedWord) (header : List Bool) (words : List SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (W : ℕ) (hB : width budget ≤ W)
    (hWords : ∀ word ∈ words,BinaryRationalOpcode.Valid word ∧ width word ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (output budget header words).1.2 steps ≤
        borrowed+BinaryPhysicalOutputLifetime.bound words.length W header.length ∧
      framePeak ((output budget header words).1.2.take steps) ≤
        BinaryPhysicalOutputLifetime.bound words.length W header.length := by
  rw [output_erases]
  exact BinaryPhysicalOutputLifetime.all_prefix budget header words hBV W hB hWords borrowed steps

theorem actual_output_work {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) (header : List Bool) :
    (output request.prepared.original.a header
      (BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar).1.1.data.toList).2 ≤
        BinaryPhysicalOutputLifetime.bound n (BinaryPRGHeapFixedProperties.wordWidth request K) header.length := by
  rw [output_work]
  exact BinaryPhysicalOutputWork.actual_output_work store request rich K outer scalar header

end Blotto.BinaryPhysicalOutputMeasured
