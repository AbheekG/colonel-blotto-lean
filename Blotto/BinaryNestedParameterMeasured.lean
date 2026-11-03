import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryQuadraticSyntaxMeasured
import Blotto.BinaryThreeReferenceMeasured
import Blotto.BinaryNestedParameterAtLifetime

/-! One measured seven-word environment feeds the actual parameter or geometry
programs and pinned returned table. Original input/location heights derive work
and enlarged source-trace bounds. Native model realization remains separate. -/
namespace Blotto.BinaryNestedParameterMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinarySyntaxUniformWork
set_option autoImplicit false
set_option maxHeartbeats 600000

abbrev Input := BinaryNestedParameters.Input

def environment (input : Input) (x : SignedWord) : (FixedArrayTable 7 SignedWord × Trace) × ℕ :=
  BinaryThreeReferenceMeasured.references 7 ![input.M,input.a,input.d,input.c,input.t,input.q,x]

theorem environment_data (input : Input) (x : SignedWord) :
    (environment input x).1.1 = BinaryNestedParameters.environment input x := BinaryThreeReferenceMeasured.references_data _ _

set_option cleanup.letToHave false in
def runProgramsWithExtras (n : ℕ) (programs : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) : ((FixedArrayTable n SignedWord × Trace) × ℕ) × ℕ :=
  let env := environment input x
  let entries := BinaryLifetimeArrayExtras.build n (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras env.1.1 (programs j))
  (((entries.1.1.1,wrap cells frames [env.1.2,entries.1.1.2]),env.2+entries.1.2+8),entries.2)

def runPrograms (n : ℕ) (programs : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) : (FixedArrayTable n SignedWord × Trace) × ℕ :=
  (runProgramsWithExtras n programs input x cells frames).1

theorem runProgramsWithExtras_compat (n : ℕ) (programs : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) :
    (runProgramsWithExtras n programs input x cells frames).1 = runPrograms n programs input x cells frames := rfl

theorem runPrograms_record (n : ℕ) (programs : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) :
    runPrograms n programs input x cells frames =
  let env := environment input x
  let entries := BinaryLifetimeArrayMeasured.build n (fun j => BinaryQuadraticSyntaxMeasured.run env.1.1 (programs j))
  ((entries.1.1,wrap cells frames [env.1.2,entries.1.2]),env.2+entries.2+8) := by
  simp only [runPrograms,runProgramsWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat]

theorem runPrograms_data (n : ℕ) (programs : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) :
    (runPrograms n programs input x cells frames).1.1 =
      (BinaryLifetimeArray.build n (fun j => BinaryQuadraticSyntaxLifetime.runWithTrace (BinaryNestedParameters.environment input x) (programs j))).1 := by
  simp only [runPrograms_record,environment_data,BinaryLifetimeArrayMeasured.build_data,BinaryQuadraticSyntaxMeasured.run_erases]

def expressionWork (s : ℕ) : ℕ := BinaryQuadraticSyntaxMeasured.workEnvelope 256 256 s 16
def expressionCells (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.bound 256 256 s 16
def expressionFrames (s : ℕ) : ℕ := BinaryQuadraticSyntaxLifetime.frames 256 s 16
def workEnvelope (n s : ℕ) : ℕ := 4124+n*expressionWork s+64*(n+1)^2+8

def envelope (n s cells frames : ℕ) : ℕ := 2193+n*expressionCells s+expressionFrames s+
  BinaryLifetimeArrayMeasured.storageReserve n+2*n+10+cells+frames+4

theorem runPrograms_bounds (n : ℕ) (programs : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s)
    (hDepth : ∀ j,(programs j).rational.depth ≤ 16)
    (hOps : ∀ j,(programs j).rational.operationBound ≤ 256) (hNodes : ∀ j,(programs j).nodes ≤ 256) :
    (runPrograms n programs input x cells frames).2 ≤ workEnvelope n s ∧
      usage (runPrograms n programs input x cells frames).1.2 ≤ envelope n s cells frames := by
  let env := environment input x
  let entries := BinaryLifetimeArrayMeasured.build n
    (fun j => BinaryQuadraticSyntaxMeasured.run (BinaryNestedParameters.environment input x) (programs j))
  have hEnvC := BinaryNestedParameters.environment_canonical input x hC hX
  have hEnvH := BinaryNestedParameterWork.environment_height input x s hH hXH
  have hEnvW : env.2 ≤ 4124 := BinaryThreeReferenceMeasured.references_work _ _
  have hEnvU : usage env.1.2 ≤ 2193 := BinaryThreeReferenceMeasured.references_usage _ _
  have hEachW := fun j => BinaryQuadraticSyntaxMeasured.run_work (BinaryNestedParameters.environment input x)
    (programs j) hEnvC s 16 256 256 hs hEnvH (hDepth j) (hOps j) (hNodes j)
  have hEachU := fun j => BinaryQuadraticSyntaxMeasured.run_bounds (BinaryNestedParameters.environment input x)
    (programs j) hEnvC s 16 256 256 hs hEnvH (hDepth j) (hOps j) (hNodes j)
  have hEntriesW := BinaryLifetimeArrayMeasured.build_work_bound n
    (fun j => BinaryQuadraticSyntaxMeasured.run (BinaryNestedParameters.environment input x) (programs j)) (expressionWork s) hEachW
  have hEntriesU := BinaryLifetimeArrayMeasured.build_bounds n
    (fun j => BinaryQuadraticSyntaxMeasured.run (BinaryNestedParameters.environment input x) (programs j))
    (expressionCells s) (expressionFrames s) (fun j => (hEachU j).1) (fun j => (hEachU j).2)
  change entries.2 ≤ _ at hEntriesW
  change usage entries.1.2 ≤ _ at hEntriesU
  have hw := wrap_usage cells frames [env.1.2,entries.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  simp only [runPrograms_record,environment_data]
  change env.2+entries.2+8 ≤ _ ∧ usage (wrap cells frames [env.1.2,entries.1.2]) ≤ _
  unfold workEnvelope envelope
  exact ⟨by omega,by omega⟩

set_option cleanup.letToHave false in
def prepareAtWithExtras (input : Input) (x : SignedWord) : ((FixedArrayTable 9 SignedWord × Trace) × ℕ) × ℕ :=
  runProgramsWithExtras 9 BinaryNestedParameters.programs input x 128 10

def prepareAt (input : Input) (x : SignedWord) : (FixedArrayTable 9 SignedWord × Trace) × ℕ :=
  (prepareAtWithExtras input x).1

theorem prepareAtWithExtras_compat (input : Input) (x : SignedWord) :
    (prepareAtWithExtras input x).1 = prepareAt input x := rfl

theorem prepareAt_record (input : Input) (x : SignedWord) :
    prepareAt input x =
  runPrograms 9 BinaryNestedParameters.programs input x 128 10 := by
  simp only [prepareAt,prepareAtWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,runProgramsWithExtras_compat]

theorem prepareAt_data (input : Input) (x : SignedWord) :
    (prepareAt input x).1.1 = (BinaryNestedParameterAtLifetime.prepareWithTrace input x).1 := by
  simp only [prepareAt_record,runPrograms_data,BinaryNestedParameterAtLifetime.prepareWithTrace]

theorem prepareAt_bounds (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s) :
    (prepareAt input x).2 ≤ workEnvelope 9 s ∧ usage (prepareAt input x).1.2 ≤ envelope 9 s 128 10 := by
  rw [prepareAt_record]
  exact (
    runPrograms_bounds 9 _ input x 128 10 hC hX s hs hH hXH
        (fun j => (BinaryNestedParameterWork.program_sizes j).1) (fun j => (BinaryNestedParameterWork.program_sizes j).2)
        BinaryNestedParameterLifetime.program_nodes

  )

set_option cleanup.letToHave false in
def prepareWithExtras (input : Input) : ((FixedArrayTable 9 SignedWord × Trace) × ℕ) × ℕ :=
  prepareAtWithExtras input BinaryRationalOpcode.zero

def prepare (input : Input) : (FixedArrayTable 9 SignedWord × Trace) × ℕ :=
  (prepareWithExtras input).1

theorem prepareWithExtras_compat (input : Input) :
    (prepareWithExtras input).1 = prepare input := rfl

theorem prepare_record (input : Input) :
    prepare input = prepareAt input BinaryRationalOpcode.zero := by
  simp only [prepare,prepareWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,runProgramsWithExtras_compat,prepareAtWithExtras_compat]

theorem prepare_data (input : Input) :
    (prepare input).1.1 = (BinaryNestedParameterLifetime.prepareWithTrace input).1 := by
  simp only [prepare_record,prepareAt_data,BinaryNestedParameterAtLifetime.prepareWithTrace,BinaryNestedParameterLifetime.prepareWithTrace]

theorem prepare_bounds (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    (prepare input).2 ≤ workEnvelope 9 s ∧ usage (prepare input).1.2 ≤ envelope 9 s 128 10 := by
  rw [prepare_record]
  exact (
    prepareAt_bounds input _ hC ⟨BinaryRationalOpcode.zero_valid,by decide⟩ s hs hH (BinaryFactoryHeight.zero_height s hs)

  )

set_option cleanup.letToHave false in
def geometryWithExtras (input : Input) (x : SignedWord) : ((FixedArrayTable 4 SignedWord × Trace) × ℕ) × ℕ :=
  runProgramsWithExtras 4 BinaryNestedParameters.firstParameters input x 96 8

def geometry (input : Input) (x : SignedWord) : (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  (geometryWithExtras input x).1

theorem geometryWithExtras_compat (input : Input) (x : SignedWord) :
    (geometryWithExtras input x).1 = geometry input x := rfl

theorem geometry_record (input : Input) (x : SignedWord) :
    geometry input x =
  runPrograms 4 BinaryNestedParameters.firstParameters input x 96 8 := by
  simp only [geometry,geometryWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,runProgramsWithExtras_compat,prepareAtWithExtras_compat,prepareWithExtras_compat]

theorem geometry_data (input : Input) (x : SignedWord) :
    (geometry input x).1.1 = (BinaryNestedParameterAtLifetime.geometryWithTrace input x).1 := by
  simp only [geometry_record,runPrograms_data,BinaryNestedParameterAtLifetime.geometryWithTrace]

theorem geometry_bounds (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s) :
    (geometry input x).2 ≤ workEnvelope 4 s ∧ usage (geometry input x).1.2 ≤ envelope 4 s 96 8 := by
  rw [geometry_record]
  exact (
    runPrograms_bounds 4 _ input x 96 8 hC hX s hs hH hXH
        (fun j => (BinaryNestedParameterWork.geometry_sizes j).1) (fun j => (BinaryNestedParameterWork.geometry_sizes j).2)
        BinaryNestedParameterAtLifetime.geometry_nodes
  )

theorem prepare_all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepare input).1.2 steps ≤ borrowed+envelope 9 s 128 10 ∧
      framePeak ((prepare input).1.2.take steps) ≤ envelope 9 s 128 10 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepare_bounds input hC s hs hH).2 borrowed steps

end Blotto.BinaryNestedParameterMeasured
