import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryQuadraticSyntaxMeasured
import Blotto.BinaryThreeReferenceMeasured
import Blotto.BinaryReflectedParameterLifetime

/-! One measured six-word environment feeds all eight measured parameter
programs and array packing. Exact prior parameter data is preserved; enlarged
source reference/control traces have direct bounds. Native model joins remain. -/

namespace Blotto.BinaryFourParametersMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryFourParameters BinarySyntaxUniformWork
set_option autoImplicit false
set_option maxHeartbeats 3500000

def environment (input : Input) : (FixedArrayTable 6 SignedWord × Trace) × ℕ :=
  BinaryThreeReferenceMeasured.references 6 ![input.B,input.u,input.v,input.w,input.ell,input.p]

theorem environment_data (input : Input) : (environment input).1.1 = input.environment :=
  BinaryThreeReferenceMeasured.references_data _ _

set_option cleanup.letToHave false in
def prepareWithExtras (input : Input) : ((FixedArrayTable 8 SignedWord × Trace) × ℕ) × ℕ :=
  let env := environment input
  let entries := BinaryLifetimeArrayExtras.build 8 (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras env.1.1 (programs j))
  (((entries.1.1.1,wrap 114 10 [env.1.2,entries.1.1.2]),env.2+entries.1.2+8),entries.2)

def prepare (input : Input) : (FixedArrayTable 8 SignedWord × Trace) × ℕ :=
  (prepareWithExtras input).1

theorem prepareWithExtras_compat (input : Input) :
    (prepareWithExtras input).1 = prepare input := rfl

theorem prepare_record (input : Input) :
    prepare input =
  let env := environment input
  let entries := BinaryLifetimeArrayMeasured.build 8 (fun j => BinaryQuadraticSyntaxMeasured.run env.1.1 (programs j))
  ((entries.1.1,wrap 114 10 [env.1.2,entries.1.2]),env.2+entries.2+8) := by
  simp only [prepare,prepareWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat]

theorem prepare_data (input : Input) :
    (prepare input).1.1 = (BinaryReflectedParameterLifetime.prepareWithTrace input).1 := by
  simp only [prepare_record,BinaryReflectedParameterLifetime.prepareWithTrace,environment_data,
    BinaryLifetimeArrayMeasured.build_data,BinaryQuadraticSyntaxMeasured.run_erases]

def expressionWork (s : ℕ) : ℕ := BinaryQuadraticSyntaxMeasured.workEnvelope 256 256 (s+1) 12
def workEnvelope (s : ℕ) : ℕ := 8*expressionWork s+8352
def expressionCells (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.bound 256 256 (s+1) 12
def expressionFrames (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.frames 256 (s+1) 12
def envelope (s : ℕ) : ℕ := 8*expressionCells s+expressionFrames s+5000

theorem environment_height (input : Input) (source : RationalFourInput) (hR : input.Refines source)
    (s : ℕ) (hH : source.FieldsHeight s) : EnvHeight input.environment (s+1) := by
  intro j
  have h := (hH.environment j).mono (by omega : s ≤ s+1)
  rw [← input_environment input source hR] at h
  simpa only [BinaryRationalExpression.interpretedEnvironment,FixedArrayTable.read_ofFn] using h

theorem prepare_bounds (input : Input) (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (prepare input).2 ≤ workEnvelope s ∧ usage (prepare input).1.2 ≤ envelope s := by
  let env := environment input
  let entries := BinaryLifetimeArrayMeasured.build 8 (fun j => BinaryQuadraticSyntaxMeasured.run input.environment (programs j))
  have hEnvW : env.2 ≤ 3160 := BinaryThreeReferenceMeasured.references_work _ _
  have hEnvU : usage env.1.2 ≤ 1703 := BinaryThreeReferenceMeasured.references_usage _ _
  have hHeight := environment_height input source hR s hH
  have hEachW := fun j => BinaryQuadraticSyntaxMeasured.run_work input.environment (programs j)
    (input_canonical input hC) (s+1) 12 256 256 (by omega) hHeight
    (BinaryReflectedParameterLifetime.program_sizes j).1 (BinaryReflectedParameterLifetime.program_sizes j).2.1
    (BinaryReflectedParameterLifetime.program_sizes j).2.2
  have hEachU := fun j => BinaryQuadraticSyntaxMeasured.run_bounds input.environment (programs j)
    (input_canonical input hC) (s+1) 12 256 256 (by omega) hHeight
    (BinaryReflectedParameterLifetime.program_sizes j).1 (BinaryReflectedParameterLifetime.program_sizes j).2.1
    (BinaryReflectedParameterLifetime.program_sizes j).2.2
  have hEntriesW := BinaryLifetimeArrayMeasured.build_work_bound 8
    (fun j => BinaryQuadraticSyntaxMeasured.run input.environment (programs j)) (expressionWork s) hEachW
  have hEntriesU := BinaryLifetimeArrayMeasured.build_bounds 8
    (fun j => BinaryQuadraticSyntaxMeasured.run input.environment (programs j)) (expressionCells s) (expressionFrames s)
    (fun j => (hEachU j).1) (fun j => (hEachU j).2)
  have hw := wrap_usage 114 10 [env.1.2,entries.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change entries.2 ≤ _ at hEntriesW
  change usage entries.1.2 ≤ _ at hEntriesU
  simp only [prepare_record,environment_data]
  change env.2+entries.2+8 ≤ _ ∧ usage (wrap 114 10 [env.1.2,entries.1.2]) ≤ _
  unfold workEnvelope envelope BinaryLifetimeArrayMeasured.storageReserve at *
  exact ⟨by omega,by omega⟩

theorem all_prefix (input : Input) (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepare input).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((prepare input).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepare_bounds input source hC hR s hs hH).2 borrowed steps

end Blotto.BinaryFourParametersMeasured
