import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryNestedResidualDescriptorMeasured
import Blotto.BinaryNestedFirstAssemblyMeasured
import Blotto.BinaryNestedResidualLifetime

/-! A shared parameter table and actual measured subtraction build the residual
five-word environment. The returned measured three-slot descriptor and its
reference padding preserve the preceding data with derived source bounds. -/
namespace Blotto.BinaryNestedResidualMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 1200000

abbrev Input := BinaryNestedParameters.Input
abbrev Small := BinaryStoredOverlapEnvironment.Segment 3 3
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def environmentFrom (input : Input) (parameters : FixedArrayTable 9 SignedWord) (difference : (SignedWord × Trace) × ℕ) :
    (FixedArrayTable 5 SignedWord × Trace) × ℕ :=
  let built := BinaryThreeReferenceMeasured.references 5 ![parameters.read 1,parameters.read 2,difference.1.1,parameters.read 0,input.t]
  ((built.1.1,wrap 32 2 [difference.1.2,built.1.2]),difference.2+built.2+8)

set_option cleanup.letToHave false in
def environmentWithExtras (input : Input) (parameters : FixedArrayTable 9 SignedWord) : ((FixedArrayTable 5 SignedWord × Trace) × ℕ) × ℕ :=
  let subtracted := BinaryNormalizedCoordinate.opcode .sub input.M input.c
  (environmentFrom input parameters subtracted.1,subtracted.2)

def environment (input : Input) (parameters : FixedArrayTable 9 SignedWord) : (FixedArrayTable 5 SignedWord × Trace) × ℕ :=
  (environmentWithExtras input parameters).1

theorem environmentWithExtras_compat (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    (environmentWithExtras input parameters).1 = environment input parameters := rfl

theorem environment_record (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    environment input parameters =
  environmentFrom input parameters (BinaryPlannedQuadratic.apply .sub input.M input.c) := by
  simp only [environment,environmentWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record]

theorem environment_data (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    (environment input parameters).1.1 = (BinaryNestedResidualLifetime.environmentWithTrace input parameters).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,environment_record,environmentFrom,BinaryNestedResidualLifetime.environmentWithTrace,
    BinaryThreeReferenceMeasured.references_data,BinaryNestedResidualLifetime.copyWithTrace_erasure,BinaryQuadraticMeasured.apply_erases]

def environmentPrice (s : ℕ) : ℕ := BinaryReflectedSystemMeasured.opcodePrice (2*s+1)+2324+8
def environmentEnvelope (s : ℕ) : ℕ := opcodeEnvelope (2*s+1)+1277+64

theorem environmentFrom_bounds (input : Input) (parameters : FixedArrayTable 9 SignedWord) (difference : (SignedWord × Trace) × ℕ)
    (P U : ℕ) (h : difference.2 ≤ P ∧ usage difference.1.2 ≤ U) :
    (environmentFrom input parameters difference).2 ≤ P+2324+8 ∧ usage (environmentFrom input parameters difference).1.2 ≤ U+1277+64 := by
  let built := BinaryThreeReferenceMeasured.references 5 ![parameters.read 1,parameters.read 2,difference.1.1,parameters.read 0,input.t]
  have hb : built.2 ≤ 2324 ∧ usage built.1.2 ≤ 1277 :=
    ⟨BinaryThreeReferenceMeasured.references_work 5 _,BinaryThreeReferenceMeasured.references_usage 5 _⟩
  have hw := wrap_usage 32 2 [difference.1.2,built.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change difference.2+built.2+8 ≤ _ ∧ usage (wrap 32 2 [difference.1.2,built.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem environment_bounds (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (s : ℕ) (hH : BinaryNestedParameterWork.InputHeight input s) :
    (environment input parameters).2 ≤ environmentPrice s ∧ usage (environment input parameters).1.2 ≤ environmentEnvelope s := by
  have hM : width input.M ≤ 2*s+1 := by have h := hC.1.2.trans (rationalWordWidth_of_height hH.1); omega
  have hCw : width input.c ≤ 2*s+1 := by have h := hC.2.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.2.1); omega
  have hResult := environmentFrom_bounds input parameters _ _ _ (BinaryReflectedSystemMeasured.opcode_bounds .sub _ _ _ hM hCw)
  simp only [environment_record, BinaryPlannedQuadratic.apply_previous]
  exact hResult

set_option cleanup.letToHave false in
def fromEnvironmentWithExtras (env : (FixedArrayTable 5 SignedWord × Trace) × ℕ) : ((Small × Trace) × ℕ) × ℕ :=
  let table := BinaryNestedResidualDescriptorMeasured.descriptorWithExtras env.1.1
  (((table.1.1.1,wrap 32 2 [env.1.2,table.1.1.2]),env.2+table.1.2+8),table.2)

def fromEnvironment (env : (FixedArrayTable 5 SignedWord × Trace) × ℕ) : (Small × Trace) × ℕ :=
  (fromEnvironmentWithExtras env).1

theorem fromEnvironmentWithExtras_compat (env : (FixedArrayTable 5 SignedWord × Trace) × ℕ) :
    (fromEnvironmentWithExtras env).1 = fromEnvironment env := rfl

theorem fromEnvironment_record (env : (FixedArrayTable 5 SignedWord × Trace) × ℕ) :
    fromEnvironment env =
  let table := BinaryNestedResidualDescriptorMeasured.descriptor env.1.1
  ((table.1.1,wrap 32 2 [env.1.2,table.1.2]),env.2+table.2+8) := by
  simp only [fromEnvironment,fromEnvironmentWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,BinaryNestedResidualDescriptorMeasured.descriptorWithExtras_compat,environmentWithExtras_compat]

set_option cleanup.letToHave false in
def residualWithExtras (input : Input) (parameters : FixedArrayTable 9 SignedWord) : ((Small × Trace) × ℕ) × ℕ :=
  let env := environmentWithExtras input parameters
  let table := fromEnvironmentWithExtras env.1
  (table.1,env.2+table.2)

def residual (input : Input) (parameters : FixedArrayTable 9 SignedWord) : (Small × Trace) × ℕ :=
  (residualWithExtras input parameters).1

theorem residualWithExtras_compat (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    (residualWithExtras input parameters).1 = residual input parameters := rfl

theorem residual_record (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    residual input parameters = fromEnvironment (environment input parameters) := by
  simp only [residual,residualWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,environmentWithExtras_compat,fromEnvironmentWithExtras_compat]

theorem residual_data (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    (residual input parameters).1.1 = (BinaryNestedResidualLifetime.residualWithTrace input parameters).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,residual_record,fromEnvironment_record,BinaryNestedResidualLifetime.residualWithTrace,
    BinaryNestedResidualDescriptorMeasured.descriptor_data,environment_data]

def workEnvelope (s : ℕ) : ℕ := environmentPrice s+BinaryNestedResidualDescriptorMeasured.workEnvelope (expressionHeightBudget s 16)+8
def envelope (s : ℕ) : ℕ := environmentEnvelope s+BinaryNestedResidualDescriptorMeasured.envelope (expressionHeightBudget s 16)+64

theorem fromEnvironment_bounds (env : (FixedArrayTable 5 SignedWord × Trace) × ℕ) (hC : ∀ j,CanonicalWord (env.1.1.read j))
    (H : ℕ) (hs : 3 ≤ H) (hHeight : BinarySyntaxUniformWork.EnvHeight env.1.1 H)
    (P U : ℕ) (hEnv : env.2 ≤ P ∧ usage env.1.2 ≤ U) :
    (fromEnvironment env).2 ≤ P+BinaryNestedResidualDescriptorMeasured.workEnvelope H+8 ∧
      usage (fromEnvironment env).1.2 ≤ U+BinaryNestedResidualDescriptorMeasured.envelope H+64 := by
  let table := BinaryNestedResidualDescriptorMeasured.descriptor env.1.1
  have hTable := BinaryNestedResidualDescriptorMeasured.descriptor_bounds env.1.1 hC H hs hHeight
  change table.2 ≤ _ ∧ usage table.1.2 ≤ _ at hTable
  have hw := wrap_usage 32 2 [env.1.2,table.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change env.2+table.2+8 ≤ _ ∧ usage (wrap 32 2 [env.1.2,table.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem residual_bounds (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    (residual input parameters).2 ≤ workEnvelope s ∧ usage (residual input parameters).1.2 ≤ envelope s := by
  let env := environment input parameters
  have hState := (environment_data input parameters).trans (BinaryNestedResidualLifetime.environmentWithTrace_erasure input parameters hC hParameters)
  have hEC : ∀ j,CanonicalWord (env.1.1.read j) := by rw [hState]; exact BinaryNestedComponents.residualEnvironment_canonical input hC
  have hEH : BinarySyntaxUniformWork.EnvHeight env.1.1 (expressionHeightBudget s 16) := by
    rw [hState]; exact BinaryNestedRemainingFactoryWork.residual_env_height input hC s hs hH
  have hResult := fromEnvironment_bounds env hEC _ (hs.trans (expressionHeightBudget_ge_input s 16)) hEH _ _ (environment_bounds input parameters hC s hH)
  simp only [residual_record,workEnvelope,envelope]
  with_reducible exact hResult

def pad (table : Small) : (Segment × Trace) × ℕ :=
  let weights := BinaryThreeReferenceMeasured.references (α := SignedWord) 9
    (fun slot => Fin.addCases (m := 3) (n := 6) table.weight.read (fun _ => BinaryRationalOpcode.zero) slot)
  let P := BinaryThreeReferenceMeasured.references (α := FixedArrayTable 3 SignedWord) 9
    (fun slot => Fin.addCases (m := 3) (n := 6) table.P.read (fun _ => table.P.read 0) slot)
  let Q := BinaryThreeReferenceMeasured.references (α := FixedArrayTable 3 SignedWord) 9
    (fun slot => Fin.addCases (m := 3) (n := 6) table.Q.read (fun _ => table.Q.read 0) slot)
  ((⟨weights.1.1,P.1.1,Q.1.1⟩,wrap 32 2 [weights.1.2,P.1.2,Q.1.2]),weights.2+P.2+Q.2+12)

theorem pad_data (table : Small) : (pad table).1.1 = (BinaryNestedResidualLifetime.padWithTrace table).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,pad,BinaryNestedResidualLifetime.padWithTrace,BinaryThreeReferenceMeasured.references_data,
    BinaryNestedResidualLifetime.copyWithTrace_erasure]

theorem pad_bounds (table : Small) : (pad table).2 ≤ 20000 ∧ usage (pad table).1.2 ≤ 11000 := by
  let weights := BinaryThreeReferenceMeasured.references (α := SignedWord) 9
    (fun slot => Fin.addCases (m := 3) (n := 6) table.weight.read (fun _ => BinaryRationalOpcode.zero) slot)
  let P := BinaryThreeReferenceMeasured.references (α := FixedArrayTable 3 SignedWord) 9
    (fun slot => Fin.addCases (m := 3) (n := 6) table.P.read (fun _ => table.P.read 0) slot)
  let Q := BinaryThreeReferenceMeasured.references (α := FixedArrayTable 3 SignedWord) 9
    (fun slot => Fin.addCases (m := 3) (n := 6) table.Q.read (fun _ => table.Q.read 0) slot)
  have hwW : weights.2 ≤ 6436 := BinaryThreeReferenceMeasured.references_work 9 _
  have hpW : P.2 ≤ 6436 := BinaryThreeReferenceMeasured.references_work 9 _
  have hqW : Q.2 ≤ 6436 := BinaryThreeReferenceMeasured.references_work 9 _
  have hwU : usage weights.1.2 ≤ 3365 := BinaryThreeReferenceMeasured.references_usage 9 _
  have hpU : usage P.1.2 ≤ 3365 := BinaryThreeReferenceMeasured.references_usage 9 _
  have hqU : usage Q.1.2 ≤ 3365 := BinaryThreeReferenceMeasured.references_usage 9 _
  have hWrap := wrap_usage 32 2 [weights.1.2,P.1.2,Q.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change weights.2+P.2+Q.2+12 ≤ _ ∧ usage (wrap 32 2 [weights.1.2,P.1.2,Q.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem all_prefix (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (residual input parameters).1.2 steps ≤ borrowed+envelope s ∧ framePeak ((residual input parameters).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (residual_bounds input parameters hC hParameters s hs hH).2 borrowed steps

end Blotto.BinaryNestedResidualMeasured
