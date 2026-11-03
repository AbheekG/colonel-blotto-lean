import Blotto.BinaryNestedProfileMeasured
import Blotto.BinaryReflectedTerminalInputMeasured
import Blotto.BinaryTerminalPermutationMeasured
import Blotto.BinaryReflectedTerminalFactoryLifetime

/-! Actual measured terminal input, complete nested profile and terminal
permutation construct the returned table once. Canonical/nonnegative sampler
certificates are erased source proofs; no factory replay attaches them. -/
namespace Blotto.BinaryReflectedTerminalFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18
abbrev Terminal := BinaryNestedParameters.Input × Equiv.Perm (Fin 3)

def collect (terminal : (Terminal × Trace) × ℕ) (nested restored : (Segment × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  ((restored.1.1,wrap 40 3 [terminal.1.2,nested.1.2,restored.1.2]),terminal.2+nested.2+restored.2+12)

set_option cleanup.letToHave false in
def fromTerminalWithExtras (terminal : (Terminal × Trace) × ℕ) (K : ℕ) (outer : BinaryScalarTape K) : ((Segment × Trace) × ℕ) × ℕ :=
  let nested := BinaryNestedProfileMeasured.profileWithExtras terminal.1.1.1 K outer
  let restored := BinaryTerminalPermutationMeasured.permute nested.1.1.1 terminal.1.1.2
  (collect terminal nested.1 restored,nested.2)

def fromTerminal (terminal : (Terminal × Trace) × ℕ) (K : ℕ) (outer : BinaryScalarTape K) : (Segment × Trace) × ℕ :=
  (fromTerminalWithExtras terminal K outer).1

theorem fromTerminalWithExtras_compat (terminal : (Terminal × Trace) × ℕ) (K : ℕ) (outer : BinaryScalarTape K) :
    (fromTerminalWithExtras terminal K outer).1 = fromTerminal terminal K outer := rfl

theorem fromTerminal_record (terminal : (Terminal × Trace) × ℕ) (K : ℕ) (outer : BinaryScalarTape K) :
    fromTerminal terminal K outer =
  let nested := BinaryNestedProfileMeasured.profile terminal.1.1.1 K outer
  let restored := BinaryTerminalPermutationMeasured.permute nested.1.1 terminal.1.1.2
  collect terminal nested restored := by
  simp only [fromTerminal,fromTerminalWithExtras,BinaryReflectedTerminalInputMeasured.terminalWithExtras_compat,BinaryNestedProfileMeasured.orderedWithExtras_compat,BinaryNestedProfileMeasured.profileWithExtras_compat]

set_option cleanup.letToHave false in
def tableWithExtras {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (K : ℕ) (outer : BinaryScalarTape K) : ((Segment × Trace) × ℕ) × ℕ :=
  let terminal := BinaryReflectedTerminalInputMeasured.terminalWithExtras cached result.state
  let produced := fromTerminalWithExtras terminal.1 K outer
  (produced.1,terminal.2+produced.2)

def table {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (K : ℕ) (outer : BinaryScalarTape K) : (Segment × Trace) × ℕ :=
  (tableWithExtras cached result K outer).1

theorem tableWithExtras_compat {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (K : ℕ) (outer : BinaryScalarTape K) :
    (tableWithExtras cached result K outer).1 = table cached result K outer := rfl

theorem table_record {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (K : ℕ) (outer : BinaryScalarTape K) :
    table cached result K outer =
  fromTerminal (BinaryReflectedTerminalInputMeasured.terminal cached result.state) K outer := by
  simp only [table,tableWithExtras,BinaryReflectedTerminalInputMeasured.terminalWithExtras_compat,BinaryNestedProfileMeasured.orderedWithExtras_compat,BinaryNestedProfileMeasured.profileWithExtras_compat,fromTerminalWithExtras_compat]

theorem table_data (input : BinaryFourParameters.Input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity) (K : ℕ) (outer : BinaryScalarTape K) :
    (table cached result K outer).1.1 = (BinaryReflectedTerminalFactoryLifetime.tableWithTrace cached result K outer).1 := by
  simp only [table_record,fromTerminal_record,collect,BinaryReflectedTerminalFactoryLifetime.tableWithTrace,
    BinaryReflectedTerminalInputMeasured.terminal_erases,BinaryNestedProfileMeasured.profile_data,BinaryTerminalPermutationMeasured.permute_data]

theorem table_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity) (K : ℕ) (outer : BinaryScalarTape K) :
    (table cached result K outer).1.1 = BinaryTerminalProfileCompiler.profile (BinaryReflectedFourSetup.prepare input) result.state K outer :=
  (table_data input cached result K outer).trans (BinaryReflectedTerminalFactoryLifetime.tableWithTrace_erasure input hC cached result K outer)

def workEnvelope (s K : ℕ) : ℕ := BinaryReflectedTerminalInputMeasured.terminalPrice (2*expressionHeightBudget s 21+1)+
  BinaryNestedProfileMeasured.workEnvelope (expressionHeightBudget s 23) K+85000+12

def envelope (s K : ℕ) : ℕ := BinaryReflectedTerminalInputLifetime.terminalEnvelope (2*expressionHeightBudget s 21+1)+
  BinaryNestedProfileMeasured.envelope (expressionHeightBudget s 23) K+50000+64

theorem collect_bounds (terminal : (Terminal × Trace) × ℕ) (nested restored : (Segment × Trace) × ℕ) (T N R U F H : ℕ)
    (ht : terminal.2 ≤ T ∧ usage terminal.1.2 ≤ U) (hn : nested.2 ≤ N ∧ usage nested.1.2 ≤ F)
    (hr : restored.2 ≤ R ∧ usage restored.1.2 ≤ H) :
    (collect terminal nested restored).2 ≤ T+N+R+12 ∧ usage (collect terminal nested restored).1.2 ≤ U+F+H+64 := by
  have hw := wrap_usage 40 3 [terminal.1.2,nested.1.2,restored.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change terminal.2+nested.2+restored.2+12 ≤ _ ∧ usage (wrap 40 3 [terminal.1.2,nested.1.2,restored.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem fromTerminal_bounds (terminal : (Terminal × Trace) × ℕ) (hC : terminal.1.1.1.Canonical) (H : ℕ) (hs : 3 ≤ H)
    (hHeight : BinaryNestedParameterWork.InputHeight terminal.1.1.1 H) (K : ℕ) (outer : BinaryScalarTape K)
    (P U : ℕ) (hTerminal : terminal.2 ≤ P ∧ usage terminal.1.2 ≤ U) :
    (fromTerminal terminal K outer).2 ≤ P+BinaryNestedProfileMeasured.workEnvelope H K+85000+12 ∧
      usage (fromTerminal terminal K outer).1.2 ≤ U+BinaryNestedProfileMeasured.envelope H K+50000+64 := by
  let nested := BinaryNestedProfileMeasured.profile terminal.1.1.1 K outer
  let restored := BinaryTerminalPermutationMeasured.permute nested.1.1 terminal.1.1.2
  have hNested := BinaryNestedProfileMeasured.profile_bounds terminal.1.1.1 hC H hs hHeight K outer
  have hRestored := BinaryTerminalPermutationMeasured.permute_bounds nested.1.1 terminal.1.1.2
  have hResult := collect_bounds terminal nested restored _ _ _ _ _ _ hTerminal hNested hRestored
  simp only [fromTerminal_record]
  with_reducible exact hResult

theorem table_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K) :
    (table cached result K outer).2 ≤ workEnvelope s K ∧ usage (table cached result K outer).1.2 ≤ envelope s K := by
  let terminal := BinaryReflectedTerminalInputMeasured.terminal cached result.state
  have hTerminal := BinaryReflectedTerminalInputMeasured.reached_bounds input source hC hR hCase s hs hH N bits result hSuccess cached
  have hState := BinaryReflectedTerminalInputMeasured.terminal_source_data cached result.state result.canonical
  have hTC : terminal.1.1.1.Canonical := by
    rw [hState]; exact BinaryNestedTerminalInput.prepare_canonical _ _ (BinaryReflectedFourSetup.prepare_canonical input hC) result.canonical
  have hTH : BinaryNestedParameterWork.InputHeight terminal.1.1.1 (expressionHeightBudget s 23) := by
    rw [hState]
    have h := BinaryNestedTerminalPreparationWork.reached_input_height input source hC hR hCase s hs hH N bits result hSuccess
    rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state] at h
    exact h
  have hResult := fromTerminal_bounds terminal hTC _ (by unfold expressionHeightBudget; omega) hTH K outer _ _ hTerminal
  simp only [table_record]
  unfold workEnvelope envelope
  with_reducible exact hResult

def attach (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K)
    (built : (Segment × Trace) × ℕ)
    (hTable : built.1.1 = BinaryTerminalProfileCompiler.profile (BinaryReflectedFourSetup.prepare input) result.state K outer) :
    (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ :=
  ((⟨built.1.1,
    (by rw [hTable]; exact BinaryTerminalProfileCompiler.profile_canonical _ _ (BinaryReflectedFourSetup.prepare_canonical input hC) result.canonical K outer),
    (by rw [hTable]; exact BinaryReflectedSerialRun.profile_nonnegative input hC hAd N bits result hSuccess K outer)⟩,built.1.2),built.2)

set_option cleanup.letToHave false in
def preparedWithExtras (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) : ((BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ) × ℕ :=
  let built := tableWithExtras cached result K outer
  (attach input hC hAd N bits result hSuccess K outer built.1
    (by simpa only [built,tableWithExtras_compat] using table_erasure input hC cached result K outer),built.2)

def prepared (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) :
    (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ :=
  (preparedWithExtras input hC hAd cached N bits result hSuccess K outer).1

theorem preparedWithExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) :
    (preparedWithExtras input hC hAd cached N bits result hSuccess K outer).1 = prepared input hC hAd cached N bits result hSuccess K outer := rfl

theorem prepared_record (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) :
    prepared input hC hAd cached N bits result hSuccess K outer =
  let built := table cached result K outer
  attach input hC hAd N bits result hSuccess K outer built (table_erasure input hC cached result K outer) := by
  simp only [prepared,preparedWithExtras,BinaryReflectedTerminalInputMeasured.terminalWithExtras_compat,BinaryNestedProfileMeasured.orderedWithExtras_compat,BinaryNestedProfileMeasured.profileWithExtras_compat,fromTerminalWithExtras_compat,tableWithExtras_compat]

theorem prepared_table (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) :
    (prepared input hC hAd cached N bits result hSuccess K outer).1.1.table = (table cached result K outer).1.1 := by
  simp only [prepared_record]
  unfold attach
  with_reducible rfl

theorem prepared_unique {n k : ℕ} (a b : BinaryStoredSegmentProgram.Prepared n k) (h : a.table = b.table) : a = b := by
  cases a with
  | mk ta ac an =>
    cases b with
    | mk bt bc bn =>
      dsimp only at h
      cases h
      rfl

theorem prepared_data (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) :
    (prepared input hC hAd cached N bits result hSuccess K outer).1.1 =
      (BinaryReflectedTerminalFactoryLifetime.preparedWithTrace input hC hAd cached N bits result hSuccess K outer).1 := by
  apply prepared_unique
  rw [prepared_table,table_data]
  rfl

theorem prepared_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K) :
    (prepared input hC hAd cached N bits result hSuccess K outer).2 ≤ workEnvelope s K ∧
      usage (prepared input hC hAd cached N bits result hSuccess K outer).1.2 ≤ envelope s K := by
  have hResult := table_bounds input source hC hR hCase s hs hH N bits result hSuccess cached K outer
  simp only [prepared_record]
  unfold attach
  with_reducible exact hResult

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (table cached result K outer).1.2 steps ≤ borrowed+envelope s K ∧ framePeak ((table cached result K outer).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (table_bounds input source hC hR hCase s hs hH N bits result hSuccess cached K outer).2 borrowed steps

end Blotto.BinaryReflectedTerminalFactoryMeasured
