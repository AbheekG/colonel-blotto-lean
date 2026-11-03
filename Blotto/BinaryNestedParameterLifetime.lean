import Blotto.BinaryNestedClassifyLifetime

/-! One actual nine-word parameter table for the ordered interior nested
factory, evaluated from the six supplied words and the zero location. -/
namespace Blotto.BinaryNestedParameterLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input

def prepareWithTrace (input : Input) : FixedArrayTable 9 SignedWord × Trace :=
  let env := BinaryNestedParameters.environment input BinaryRationalOpcode.zero
  let entries := BinaryLifetimeArray.build 9
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.programs j))
  (entries.1,wrap 128 10 [entries.2])

theorem prepareWithTrace_erasure (input : Input) (hC : input.Canonical) :
    (prepareWithTrace input).1 = BinaryNestedProfileCompiler.parameters input := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [prepareWithTrace,BinaryLifetimeArray.build_erases,
    BinaryNestedProfileCompiler.parameters,BinaryNestedParameters.prepare,FixedArrayTable.read_ofFn]
  exact BinaryQuadraticSyntaxLifetime.runWithTrace_state _ _
    (BinaryNestedParameters.environment_canonical input BinaryRationalOpcode.zero hC
      ⟨BinaryRationalOpcode.zero_valid,by decide⟩)

theorem program_nodes (j : Fin 9) : (BinaryNestedParameters.programs j).nodes ≤ 256 := by
  fin_cases j <;> decide

def envelope (s : ℕ) : ℕ :=
  9 * (BinaryQuadraticSyntaxLifetime.bound 256 256 s 16 +
    BinaryQuadraticSyntaxLifetime.frames 256 s 16) + 768

theorem prepareWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (prepareWithTrace input).2 ≤ envelope s := by
  let env := BinaryNestedParameters.environment input BinaryRationalOpcode.zero
  have hEnv := BinaryNestedParameters.environment_canonical input BinaryRationalOpcode.zero hC
    (show CanonicalWord BinaryRationalOpcode.zero from ⟨BinaryRationalOpcode.zero_valid,by decide⟩)
  have hHeight := BinaryNestedParameterWork.environment_height input BinaryRationalOpcode.zero s hH
    (BinaryFactoryHeight.zero_height s hs)
  have hEach := fun j => BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env
    (BinaryNestedParameters.programs j) hEnv s 16 256 256 hs hHeight
    (BinaryNestedParameterWork.program_sizes j).1
    (BinaryNestedParameterWork.program_sizes j).2 (program_nodes j)
  have hArray := array_usage 9
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.programs j))
    (BinaryQuadraticSyntaxLifetime.bound 256 256 s 16)
    (BinaryQuadraticSyntaxLifetime.frames 256 s 16)
    (fun j => (hEach j).1) (fun j => (hEach j).2)
  have hw := wrap_usage 128 10
    [(BinaryLifetimeArray.build 9
      (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.programs j))).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 128 10
    [(BinaryLifetimeArray.build 9
      (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.programs j))).2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace input).2 steps ≤ borrowed + envelope s ∧
    framePeak ((prepareWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (prepareWithTrace_usage input hC s hs hH) borrowed steps

end Blotto.BinaryNestedParameterLifetime
