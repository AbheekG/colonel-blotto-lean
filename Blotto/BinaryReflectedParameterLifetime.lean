import Blotto.BinaryLifetimeUsage
import Blotto.BinaryFourParameters

/-! The eight reflected parameter programs consume one actual environment
and the traced quadratic compiler/evaluator. Source field heights and the
fixed program sizes derive the complete retained allocation reservation. -/
namespace Blotto.BinaryReflectedParameterLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryFourParameters BinaryPRGHeapTraceUsage BinaryLifetimeUsage
open BinarySyntaxUniformWork
set_option maxHeartbeats 2000000

def prepareWithTrace (input : Input) : FixedArrayTable 8 SignedWord × Trace :=
  let environment := input.environment
  let entries := BinaryLifetimeArray.build 8
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace environment (programs j))
  (entries.1,wrap 114 10 [entries.2])

theorem prepareWithTrace_erasure (input : Input) (hC : input.Canonical) :
    (prepareWithTrace input).1 = prepare input := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [prepareWithTrace,BinaryLifetimeArray.build_erases,prepare,FixedArrayTable.read_ofFn]
  exact BinaryQuadraticSyntaxLifetime.runWithTrace_state input.environment (programs j) (input_canonical input hC)

theorem program_sizes (j : Fin 8) :
    (programs j).rational.depth ≤ 12 ∧ (programs j).rational.operationBound ≤ 256 ∧ (programs j).nodes ≤ 256 := by
  fin_cases j <;> decide

def envelope (s : ℕ) : ℕ :=
  8 * (BinaryQuadraticSyntaxLifetime.bound 256 256 (s + 1) 12 +
    BinaryQuadraticSyntaxLifetime.frames 256 (s + 1) 12) + 512

theorem prepareWithTrace_usage (input : Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s)
    (hH : source.FieldsHeight s) : usage (prepareWithTrace input).2 ≤ envelope s := by
  have hEnvironment : EnvHeight input.environment (s + 1) := by
    intro j
    have he := (hH.environment j).mono (by omega : s ≤ s + 1)
    rw [← input_environment input source hR] at he
    simpa only [BinaryRationalExpression.interpretedEnvironment,FixedArrayTable.read_ofFn] using he
  have hEach := fun j => BinaryQuadraticSyntaxLifetime.runWithTrace_bounds input.environment (programs j)
    (input_canonical input hC) (s + 1) 12 256 256 (by omega) hEnvironment
    (program_sizes j).1 (program_sizes j).2.1 (program_sizes j).2.2
  have hArray := array_usage 8 (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace input.environment (programs j))
    (BinaryQuadraticSyntaxLifetime.bound 256 256 (s + 1) 12)
    (BinaryQuadraticSyntaxLifetime.frames 256 (s + 1) 12) (fun j => (hEach j).1) (fun j => (hEach j).2)
  have hw := wrap_usage 114 10 [(BinaryLifetimeArray.build 8
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace input.environment (programs j))).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 114 10 [(BinaryLifetimeArray.build 8
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace input.environment (programs j))).2]) ≤ _
  unfold envelope
  omega

end Blotto.BinaryReflectedParameterLifetime
