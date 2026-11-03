import Blotto.BinaryThreeReferenceLifetime
import Blotto.BinaryGroupInputs

/-! The actual two-group factory builds all nine padded weights and both
endpoint tables from borrowed budget/literal words. Every row/array prefix
and source result record is retained; no arithmetic or descriptor is replayed. -/
namespace Blotto.BinaryUniformPairLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 1500000

def rowWithTrace (first second : SignedWord) : FixedArrayTable 2 SignedWord × Trace :=
  BinaryLifetimeArray.build 2 (fun j => ((![first,second] : Fin 2 → SignedWord) j,wrap 8 1 []))

theorem rowWithTrace_usage (first second : SignedWord) : usage (rowWithTrace first second).2 ≤ 51 :=
  array_usage 2 (fun j => ((![first,second] : Fin 2 → SignedWord) j,wrap 8 1 [])) 8 1
    (by intro j; simp [wrap,combine,listCells,arraySlots]) (by intro j; simp [wrap,combine,framePeak])

def rowsWithTrace (first second : SignedWord) : FixedArrayTable 9 (FixedArrayTable 2 SignedWord) × Trace :=
  BinaryLifetimeArray.build 9 (fun _ => rowWithTrace first second)

theorem rowsWithTrace_usage (first second : SignedWord) : usage (rowsWithTrace first second).2 ≤ 768 := by
  have hr := rowWithTrace_usage first second
  have hb : listCells (rowWithTrace first second).2 + arraySlots (rowWithTrace first second).2 ≤ 51 := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells at hr
    omega
  have hf : framePeak (rowWithTrace first second).2 ≤ 51 := by unfold usage at hr; omega
  have h := array_usage 9 (fun _ => rowWithTrace first second) 51 51 (fun _ => hb) (fun _ => hf)
  exact h.trans (by omega)

def descriptorWithTrace (input : BinaryGroupInputs.UniformInput 2) : BinaryStoredOverlapEnvironment.Segment 2 9 × Trace :=
  let weights := BinaryThreeReferenceLifetime.weightsWithTrace
  let first := rowsWithTrace BinaryRationalOpcode.zero input.budget
  let second := rowsWithTrace input.budget BinaryRationalOpcode.zero
  (⟨weights.1,first.1,second.1⟩,wrap 32 2 [weights.2,first.2,second.2])

theorem descriptorWithTrace_erasure (input : BinaryGroupInputs.UniformInput 2) :
    (descriptorWithTrace input).1 = BinarySegmentAssembly.padRight (BinaryGroupInputs.pair input) 8 0 := by
  simp only [descriptorWithTrace,BinaryThreeReferenceLifetime.weightsWithTrace,rowsWithTrace,rowWithTrace,
    BinaryLifetimeArray.build_erases,BinarySegmentAssembly.padRight,BinaryGroupInputs.pair]
  congr 1

theorem descriptorWithTrace_usage (input : BinaryGroupInputs.UniformInput 2) : usage (descriptorWithTrace input).2 ≤ 4096 := by
  have hwg := BinaryThreeReferenceLifetime.weightsWithTrace_usage
  have hp := rowsWithTrace_usage BinaryRationalOpcode.zero input.budget
  have hq := rowsWithTrace_usage input.budget BinaryRationalOpcode.zero
  have hw := wrap_usage 32 2 [BinaryThreeReferenceLifetime.weightsWithTrace.2,
    (rowsWithTrace BinaryRationalOpcode.zero input.budget).2,(rowsWithTrace input.budget BinaryRationalOpcode.zero).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [BinaryThreeReferenceLifetime.weightsWithTrace.2,
    (rowsWithTrace BinaryRationalOpcode.zero input.budget).2,(rowsWithTrace input.budget BinaryRationalOpcode.zero).2]) ≤ _
  omega

end Blotto.BinaryUniformPairLifetime
