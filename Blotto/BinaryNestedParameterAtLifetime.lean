import Blotto.BinaryNestedParameterLifetime

/-! Traced nine-parameter and four-geometry syntax tables at an arbitrary
stored location word. The ordered first/family factories reuse these producers. -/
namespace Blotto.BinaryNestedParameterAtLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input

def prepareWithTrace (input : Input) (x : SignedWord) : FixedArrayTable 9 SignedWord × Trace :=
  let env := BinaryNestedParameters.environment input x
  let entries := BinaryLifetimeArray.build 9
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.programs j))
  (entries.1,wrap 128 10 [entries.2])

theorem prepareWithTrace_erasure (input : Input) (x : SignedWord)
    (hC : input.Canonical) (hX : CanonicalWord x) :
    (prepareWithTrace input x).1 = BinaryNestedParameters.prepare input x := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [prepareWithTrace,BinaryLifetimeArray.build_erases,
    BinaryNestedParameters.prepare,FixedArrayTable.read_ofFn]
  exact BinaryQuadraticSyntaxLifetime.runWithTrace_state _ _
    (BinaryNestedParameters.environment_canonical input x hC hX)

theorem prepareWithTrace_usage (input : Input) (x : SignedWord)
    (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hXH : RationalHeight (value x) s) :
    usage (prepareWithTrace input x).2 ≤ BinaryNestedParameterLifetime.envelope s := by
  let env := BinaryNestedParameters.environment input x
  have hEnv := BinaryNestedParameters.environment_canonical input x hC hX
  have hHeight := BinaryNestedParameterWork.environment_height input x s hH hXH
  have hEach := fun j => BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env
    (BinaryNestedParameters.programs j) hEnv s 16 256 256 hs hHeight
    (BinaryNestedParameterWork.program_sizes j).1
    (BinaryNestedParameterWork.program_sizes j).2
    (BinaryNestedParameterLifetime.program_nodes j)
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
  unfold BinaryNestedParameterLifetime.envelope
  omega

def geometryWithTrace (input : Input) (x : SignedWord) : FixedArrayTable 4 SignedWord × Trace :=
  let env := BinaryNestedParameters.environment input x
  let entries := BinaryLifetimeArray.build 4
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.firstParameters j))
  (entries.1,wrap 96 8 [entries.2])

theorem geometryWithTrace_erasure (input : Input) (x : SignedWord)
    (hC : input.Canonical) (hX : CanonicalWord x) :
    (geometryWithTrace input x).1 = BinaryNestedParameters.geometry input x := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [geometryWithTrace,BinaryLifetimeArray.build_erases,
    BinaryNestedParameters.geometry,FixedArrayTable.read_ofFn]
  exact BinaryQuadraticSyntaxLifetime.runWithTrace_state _ _
    (BinaryNestedParameters.environment_canonical input x hC hX)

theorem geometry_nodes (j : Fin 4) : (BinaryNestedParameters.firstParameters j).nodes ≤ 256 := by
  fin_cases j <;> decide

def geometryEnvelope (s : ℕ) : ℕ :=
  4 * (BinaryQuadraticSyntaxLifetime.bound 256 256 s 16 +
    BinaryQuadraticSyntaxLifetime.frames 256 s 16) + 384

theorem geometryWithTrace_usage (input : Input) (x : SignedWord)
    (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hXH : RationalHeight (value x) s) :
    usage (geometryWithTrace input x).2 ≤ geometryEnvelope s := by
  let env := BinaryNestedParameters.environment input x
  have hEnv := BinaryNestedParameters.environment_canonical input x hC hX
  have hHeight := BinaryNestedParameterWork.environment_height input x s hH hXH
  have hEach := fun j => BinaryQuadraticSyntaxLifetime.runWithTrace_bounds env
    (BinaryNestedParameters.firstParameters j) hEnv s 16 256 256 hs hHeight
    (BinaryNestedParameterWork.geometry_sizes j).1
    (BinaryNestedParameterWork.geometry_sizes j).2 (geometry_nodes j)
  have hArray := array_usage 4
    (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.firstParameters j))
    (BinaryQuadraticSyntaxLifetime.bound 256 256 s 16)
    (BinaryQuadraticSyntaxLifetime.frames 256 s 16)
    (fun j => (hEach j).1) (fun j => (hEach j).2)
  have hw := wrap_usage 96 8
    [(BinaryLifetimeArray.build 4
      (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.firstParameters j))).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 96 8
    [(BinaryLifetimeArray.build 4
      (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace env (BinaryNestedParameters.firstParameters j))).2]) ≤ _
  unfold geometryEnvelope
  omega

theorem prepare_all_prefix (input : Input) (x : SignedWord)
    (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hXH : RationalHeight (value x) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace input x).2 steps ≤
      borrowed + BinaryNestedParameterLifetime.envelope s ∧
    framePeak ((prepareWithTrace input x).2.take steps) ≤
      BinaryNestedParameterLifetime.envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (prepareWithTrace_usage input x hC hX s hs hH hXH) borrowed steps

end Blotto.BinaryNestedParameterAtLifetime
