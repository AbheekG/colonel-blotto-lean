import Blotto.BinaryNestedResidualDescriptorLifetime

/-! The third regime constructs the residual environment from the shared
parameter table and a traced subtraction, then produces and pads its actual
three-slot residual descriptor. -/
namespace Blotto.BinaryNestedResidualLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Small := BinaryStoredOverlapEnvironment.Segment 3 3
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def copyWithTrace {α : Type*} (n : ℕ) (values : Fin n → α) : FixedArrayTable n α × Trace :=
  BinaryLifetimeArray.build n (fun j => (values j,wrap 8 1 []))

theorem copyWithTrace_erasure {α : Type*} (n : ℕ) (values : Fin n → α) :
    (copyWithTrace n values).1 = FixedArrayTable.ofFn values := by
  simpa only [copyWithTrace] using
    (BinaryLifetimeArray.build_erases n (fun j => (values j,wrap 8 1 [])))

def copyEnvelope (n : ℕ) : ℕ := 2 * (n + 1)^2 + 10 * n + 64

theorem copyWithTrace_usage {α : Type*} (n : ℕ) (values : Fin n → α) :
    usage (copyWithTrace n values).2 ≤ copyEnvelope n := by
  let produce : Fin n → α × Trace := fun j => (values j,wrap 8 1 [])
  have hCells : ∀ j,listCells (produce j).2 + arraySlots (produce j).2 ≤ 8 := by
    intro j
    change listCells (wrap 8 1 []) + arraySlots (wrap 8 1 []) ≤ 8
    simp [wrap,combine,listCells,arraySlots]
  have hFrames : ∀ j,framePeak (produce j).2 ≤ 1 := by
    intro j
    change framePeak (wrap 8 1 []) ≤ 1
    simp [wrap,combine,framePeak]
  have ha := array_usage n produce 8 1 hCells hFrames
  change usage (BinaryLifetimeArray.build n produce).2 ≤ _
  unfold copyEnvelope
  omega

def environmentWithTrace (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    FixedArrayTable 5 SignedWord × Trace :=
  let difference := BinaryQuadraticLifetime.applyWithTrace .sub input.M input.c
  let built := copyWithTrace 5
    ![parameters.read 1,parameters.read 2,difference.1,parameters.read 0,input.t]
  (built.1,wrap 32 2 [difference.2,built.2])

theorem environmentWithTrace_erasure (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input) :
    (environmentWithTrace input parameters).1 = BinaryNestedComponents.residualEnvironment input := by
  subst parameters
  simp only [environmentWithTrace,copyWithTrace_erasure,
    BinaryQuadraticLifetime.applyWithTrace_state .sub _ _ hC.1.1 hC.2.2.2.1.1,
    BinaryNestedComponents.residualEnvironment,BinaryNestedProfileCompiler.parameters]

def environmentEnvelope (s : ℕ) : ℕ := opcodeEnvelope (2*s+1) + copyEnvelope 5 + 128

theorem environmentWithTrace_usage (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical) (s : ℕ) (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (environmentWithTrace input parameters).2 ≤ environmentEnvelope s := by
  have hM : width input.M ≤ 2*s+1 := by
    have h := hC.1.2.trans (rationalWordWidth_of_height hH.1)
    omega
  have hCWidth : width input.c ≤ 2*s+1 := by
    have h := hC.2.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.2.1)
    omega
  let difference := BinaryQuadraticLifetime.applyWithTrace .sub input.M input.c
  let built := copyWithTrace 5
    ![parameters.read 1,parameters.read 2,difference.1,parameters.read 0,input.t]
  have hDifference := opcode_usage .sub input.M input.c (2*s+1) hM hCWidth
  change usage difference.2 ≤ _ at hDifference
  have hBuilt := copyWithTrace_usage 5
    ![parameters.read 1,parameters.read 2,difference.1,parameters.read 0,input.t]
  change usage built.2 ≤ _ at hBuilt
  have hw := wrap_usage 32 2 [difference.2,built.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [difference.2,built.2]) ≤ _
  unfold environmentEnvelope
  omega

def residualWithTrace (input : Input) (parameters : FixedArrayTable 9 SignedWord) : Small × Trace :=
  let env := environmentWithTrace input parameters
  let table := BinaryNestedResidualDescriptorLifetime.descriptorWithTrace env.1
  (table.1,wrap 32 2 [env.2,table.2])

theorem residualWithTrace_erasure (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input) :
    (residualWithTrace input parameters).1 = BinaryNestedComponents.residualLottery input := by
  have hEnv := environmentWithTrace_erasure input parameters hC hParameters
  have hEnvC : ∀ j,CanonicalWord ((environmentWithTrace input parameters).1.read j) := by
    rw [hEnv]
    exact BinaryNestedComponents.residualEnvironment_canonical input hC
  unfold residualWithTrace BinaryNestedComponents.residualLottery
  dsimp only
  rw [BinaryNestedResidualDescriptorLifetime.descriptorWithTrace_erasure _ hEnvC,hEnv]

def envelope (s : ℕ) : ℕ := environmentEnvelope s +
  BinaryNestedResidualDescriptorLifetime.envelope (expressionHeightBudget s 16) + 128

theorem residualWithTrace_usage (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (residualWithTrace input parameters).2 ≤ envelope s := by
  let env := environmentWithTrace input parameters
  have hEnv := environmentWithTrace_usage input parameters hC s hH
  change usage env.2 ≤ _ at hEnv
  have hEnvState := environmentWithTrace_erasure input parameters hC hParameters
  have hEnvC : ∀ j,CanonicalWord (env.1.read j) := by
    rw [hEnvState]
    exact BinaryNestedComponents.residualEnvironment_canonical input hC
  have hEnvH : BinarySyntaxUniformWork.EnvHeight env.1 (expressionHeightBudget s 16) := by
    rw [hEnvState]
    exact BinaryNestedRemainingFactoryWork.residual_env_height input hC s hs hH
  have hTable := BinaryNestedResidualDescriptorLifetime.descriptorWithTrace_usage env.1 hEnvC
    _ (hs.trans (expressionHeightBudget_ge_input s 16)) hEnvH
  have hw := wrap_usage 32 2
    [env.2,(BinaryNestedResidualDescriptorLifetime.descriptorWithTrace env.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [env.2,(BinaryNestedResidualDescriptorLifetime.descriptorWithTrace env.1).2]) ≤ _
  unfold envelope
  omega

def padWithTrace (table : Small) : Segment × Trace :=
  let weight := copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.weight.read (fun _ : Fin 6 => BinaryRationalOpcode.zero))
  let first := copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.P.read (fun _ : Fin 6 => table.P.read 0))
  let second := copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.Q.read (fun _ : Fin 6 => table.Q.read 0))
  (⟨weight.1,first.1,second.1⟩,wrap 32 2 [weight.2,first.2,second.2])

theorem padWithTrace_erasure (table : Small) :
    (padWithTrace table).1 = BinarySegmentAssembly.padRight table 6 0 := by
  simp only [padWithTrace,copyWithTrace_erasure,BinarySegmentAssembly.padRight]

theorem padWithTrace_usage (table : Small) : usage (padWithTrace table).2 ≤ 2048 := by
  have hwg := copyWithTrace_usage 9 (Fin.addCases (m := 3) (n := 6) table.weight.read (fun _ : Fin 6 => BinaryRationalOpcode.zero))
  have hp := copyWithTrace_usage 9 (Fin.addCases (m := 3) (n := 6) table.P.read (fun _ : Fin 6 => table.P.read 0))
  have hq := copyWithTrace_usage 9 (Fin.addCases (m := 3) (n := 6) table.Q.read (fun _ : Fin 6 => table.Q.read 0))
  have hw := wrap_usage 32 2
    [(copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.weight.read (fun _ : Fin 6 => BinaryRationalOpcode.zero))).2,
      (copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.P.read (fun _ : Fin 6 => table.P.read 0))).2,
      (copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.Q.read (fun _ : Fin 6 => table.Q.read 0))).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [(copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.weight.read (fun _ : Fin 6 => BinaryRationalOpcode.zero))).2,
      (copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.P.read (fun _ : Fin 6 => table.P.read 0))).2,
      (copyWithTrace 9 (Fin.addCases (m := 3) (n := 6) table.Q.read (fun _ : Fin 6 => table.Q.read 0))).2]) ≤ _
  unfold copyEnvelope at *
  omega

theorem all_prefix (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (residualWithTrace input parameters).2 steps ≤ borrowed + envelope s ∧
    framePeak ((residualWithTrace input parameters).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (residualWithTrace_usage input parameters hC hParameters s hs hH) borrowed steps

end Blotto.BinaryNestedResidualLifetime
