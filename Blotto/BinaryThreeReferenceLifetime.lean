import Blotto.BinaryLifetimeUsage
import Blotto.BinaryThreeSpecCompiler

/-! Actual fixed three-coordinate reference arrays for exceptional endpoints
and order restoration. Words remain borrowed; all new row/table regions and
source records are reserved, without a reclamation premise. -/
namespace Blotto.BinaryThreeReferenceLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryLifetimeUsage
open BinaryExpressionCompiler
set_option maxHeartbeats 1500000

def rowWithTrace (first second third : SignedWord) : FixedArrayTable 3 SignedWord × Trace :=
  BinaryLifetimeArray.build 3 (fun j => ((![first,second,third] : Fin 3 → SignedWord) j,wrap 8 1 []))

theorem rowWithTrace_erasure (first second third : SignedWord) :
    (rowWithTrace first second third).1 = FixedArrayTable.ofFn ![first,second,third] := rfl

theorem rowWithTrace_usage (first second third : SignedWord) : usage (rowWithTrace first second third).2 ≤ 74 := by
  have h := array_usage 3 (fun j => ((![first,second,third] : Fin 3 → SignedWord) j,wrap 8 1 [])) 8 1
    (by intro j; simp [wrap,combine,listCells,arraySlots]) (by intro j; simp [wrap,combine,framePeak])
  exact h

def rowsWithTrace (first second third : SignedWord) : FixedArrayTable 9 (FixedArrayTable 3 SignedWord) × Trace :=
  BinaryLifetimeArray.build 9 (fun _ => rowWithTrace first second third)

theorem rowsWithTrace_usage (first second third : SignedWord) : usage (rowsWithTrace first second third).2 ≤ 1024 := by
  have hr := rowWithTrace_usage first second third
  have hb : listCells (rowWithTrace first second third).2 + arraySlots (rowWithTrace first second third).2 ≤ 74 := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells at hr
    omega
  have hf : framePeak (rowWithTrace first second third).2 ≤ 74 := by
    unfold usage at hr
    omega
  have h := array_usage 9 (fun _ => rowWithTrace first second third) 74 74 (fun _ => hb) (fun _ => hf)
  exact h.trans (by omega)

def weightsWithTrace : FixedArrayTable 9 SignedWord × Trace :=
  BinaryLifetimeArray.build 9 (fun slot => (if slot = 0 then Constant.one.word else Constant.zero.word,wrap 8 1 []))

theorem weightsWithTrace_usage : usage weightsWithTrace.2 ≤ 320 := by
  have h := array_usage 9 (fun slot => (if slot = 0 then Constant.one.word else Constant.zero.word,wrap 8 1 [])) 8 1
    (by intro slot; simp [wrap,combine,listCells,arraySlots]) (by intro slot; simp [wrap,combine,framePeak])
  exact h.trans (by omega)

def exceptionalWithTrace (input : BinaryThreeInputCompiler.Input) : BinaryStoredOverlapEnvironment.Segment 3 9 × Trace :=
  let weights := weightsWithTrace
  let first := rowsWithTrace Constant.zero.word Constant.zero.word input.B
  let second := rowsWithTrace input.a input.d Constant.zero.word
  (⟨weights.1,first.1,second.1⟩,wrap 32 2 [weights.2,first.2,second.2])

theorem exceptionalWithTrace_erasure (input : BinaryThreeInputCompiler.Input) :
    (exceptionalWithTrace input).1 = BinaryThreeInputCompiler.exceptional input := rfl

theorem exceptionalWithTrace_usage (input : BinaryThreeInputCompiler.Input) : usage (exceptionalWithTrace input).2 ≤ 4096 := by
  have hwg := weightsWithTrace_usage
  have hp := rowsWithTrace_usage Constant.zero.word Constant.zero.word input.B
  have hq := rowsWithTrace_usage input.a input.d Constant.zero.word
  have hw := wrap_usage 32 2 [weightsWithTrace.2,(rowsWithTrace Constant.zero.word Constant.zero.word input.B).2,
    (rowsWithTrace input.a input.d Constant.zero.word).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [weightsWithTrace.2,(rowsWithTrace Constant.zero.word Constant.zero.word input.B).2,
    (rowsWithTrace input.a input.d Constant.zero.word).2]) ≤ _
  omega

def swapRowsWithTrace (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) : FixedArrayTable 9 (FixedArrayTable 3 SignedWord) × Trace :=
  BinaryLifetimeArray.build 9 (fun slot => rowWithTrace ((rows.read slot).read 1) ((rows.read slot).read 0) ((rows.read slot).read 2))

theorem swapRowsWithTrace_usage (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) : usage (swapRowsWithTrace rows).2 ≤ 1024 := by
  have hr := fun slot => rowWithTrace_usage ((rows.read slot).read 1) ((rows.read slot).read 0) ((rows.read slot).read 2)
  have h := array_usage 9 (fun slot => rowWithTrace ((rows.read slot).read 1) ((rows.read slot).read 0) ((rows.read slot).read 2)) 74 74
    (by intro slot; have h := hr slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro slot; have h := hr slot; unfold usage at h; omega)
  exact h.trans (by omega)

def swapWithTrace (segment : BinaryStoredOverlapEnvironment.Segment 3 9) : BinaryStoredOverlapEnvironment.Segment 3 9 × Trace :=
  let first := swapRowsWithTrace segment.P
  let second := swapRowsWithTrace segment.Q
  (⟨segment.weight,first.1,second.1⟩,wrap 32 2 [first.2,second.2])

theorem swapWithTrace_erasure (segment : BinaryStoredOverlapEnvironment.Segment 3 9) :
    (swapWithTrace segment).1 = BinaryThreeSpecCompiler.swap segment := rfl

theorem swapWithTrace_usage (segment : BinaryStoredOverlapEnvironment.Segment 3 9) : usage (swapWithTrace segment).2 ≤ 4096 := by
  have hp := swapRowsWithTrace_usage segment.P
  have hq := swapRowsWithTrace_usage segment.Q
  have hw := wrap_usage 32 2 [(swapRowsWithTrace segment.P).2,(swapRowsWithTrace segment.Q).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [(swapRowsWithTrace segment.P).2,(swapRowsWithTrace segment.Q).2]) ≤ _
  omega

end Blotto.BinaryThreeReferenceLifetime
