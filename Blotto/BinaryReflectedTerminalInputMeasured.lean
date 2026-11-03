import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryReflectedFocusMeasured
import Blotto.BinaryReflectedSystemMeasured
import Blotto.BinaryReflectedTerminalInputLifetime

/-! The reached measured focus, two numerator scans and probability division
produce the actual nested terminal words and permutation once. Full old
word/trace erasure and original-field source bounds are retained. -/
namespace Blotto.BinaryReflectedTerminalInputMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 600000

def endpoint (system : BinaryReflectedFourSetup.System) (state : BinaryThreeResourceState.State) (j : Fin 3) :
    (SignedWord × Trace) × ℕ :=
  let nonzero := BooleanFreshSeedMeasured.scan (state.resource.read j).numerator
  ((if nonzero.1.1 then system.short.read j else system.long.read j,wrap 8 2 [nonzero.1.2]),nonzero.2+8)

theorem endpoint_erases (system : BinaryReflectedFourSetup.System) (state : BinaryThreeResourceState.State) (j : Fin 3) :
    (endpoint system state j).1 = BinaryReflectedTerminalInputLifetime.endpointWithTrace system state j := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,endpoint,BinaryReflectedTerminalInputLifetime.endpointWithTrace,BooleanFreshSeedMeasured.scan_erases]

def endpointPrice (W : ℕ) : ℕ := 4*(W+1)+8

theorem endpoint_work (system : BinaryReflectedFourSetup.System) (state : BinaryThreeResourceState.State)
    (j : Fin 3) (W : ℕ) (hW : width (state.resource.read j) ≤ W) : (endpoint system state j).2 ≤ endpointPrice W := by
  have hScan := BooleanFreshSeedMeasured.scan_bound (state.resource.read j).numerator
  have hLen : (state.resource.read j).numerator.length ≤ W := by unfold width at hW; omega
  change (BooleanFreshSeedMeasured.scan (state.resource.read j).numerator).2+8 ≤ _
  unfold endpointPrice
  omega

def collect {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (selected : (Fin 3 × Trace) × ℕ) (first second probability : (SignedWord × Trace) × ℕ) :
    ((BinaryNestedParameters.Input × Equiv.Perm (Fin 3)) × Trace) × ℕ :=
  ((⟨⟨prepared.system.M,first.1.1,second.1.1,prepared.system.long.read selected.1.1,
      prepared.system.short.read selected.1.1,probability.1.1⟩,Equiv.swap selected.1.1 2⟩,
    wrap 40 3 [selected.1.2,first.1.2,second.1.2,probability.1.2]),selected.2+first.2+second.2+probability.2+24)

set_option cleanup.letToHave false in
def terminalWithExtras {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) : (((BinaryNestedParameters.Input × Equiv.Perm (Fin 3)) × Trace) × ℕ) × ℕ :=
  let selected := BinaryReflectedFocusMeasured.preparedFocus prepared state
  let pi := Equiv.swap selected.1.1 2
  let first := endpoint prepared.system state (pi 0)
  let second := endpoint prepared.system state (pi 1)
  let probability := BinaryNormalizedCoordinate.opcode .div (state.resource.read selected.1.1) (prepared.capacity.read selected.1.1)
  (collect prepared selected first second probability.1,probability.2)

def terminal {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) : ((BinaryNestedParameters.Input × Equiv.Perm (Fin 3)) × Trace) × ℕ :=
  (terminalWithExtras prepared state).1

theorem terminalWithExtras_compat {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) :
    (terminalWithExtras prepared state).1 = terminal prepared state := rfl

theorem terminal_record {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) :
    terminal prepared state =
  let selected := BinaryReflectedFocusMeasured.preparedFocus prepared state
  let pi := Equiv.swap selected.1.1 2
  let first := endpoint prepared.system state (pi 0)
  let second := endpoint prepared.system state (pi 1)
  let probability := BinaryPlannedQuadratic.apply .div (state.resource.read selected.1.1) (prepared.capacity.read selected.1.1)
  collect prepared selected first second probability := by
  simp only [terminal,terminalWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record]

theorem terminal_eq {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) : terminal prepared state =
      let selected := BinaryReflectedFocusMeasured.preparedFocus prepared state
      let pi := Equiv.swap selected.1.1 2
      collect prepared selected (endpoint prepared.system state (pi 0)) (endpoint prepared.system state (pi 1))
        (BinaryQuadraticMeasured.apply .div (state.resource.read selected.1.1) (prepared.capacity.read selected.1.1)) := by
  simp only [terminal_record, BinaryPlannedQuadratic.apply_previous]

theorem terminal_erases {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) :
    (terminal prepared state).1 = BinaryReflectedTerminalInputLifetime.terminalWithTrace prepared state := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,terminal_record,collect,BinaryReflectedTerminalInputLifetime.terminalWithTrace,
    BinaryReflectedFocusMeasured.preparedFocus_erases,endpoint_erases,BinaryQuadraticMeasured.apply_erases]

theorem terminal_source_data {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) (hState : ∀ j,CanonicalWord (state.resource.read j)) :
    (terminal prepared state).1.1 =
      (BinaryNestedTerminalInput.prepare (BinaryReflectedFourSetup.prepare input) state,
        BinaryNestedTerminalInput.permutation (BinaryReflectedFourSetup.prepare input) state) := by
  rw [terminal_erases]
  exact BinaryReflectedTerminalInputLifetime.terminalWithTrace_erasure prepared state hState

def terminalPrice (W : ℕ) : ℕ := BinaryReflectedFocusMeasured.focusPrice W+2*endpointPrice W+
  BinaryReflectedSystemMeasured.opcodePrice W+24

theorem collect_work {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (selected : (Fin 3 × Trace) × ℕ) (first second probability : (SignedWord × Trace) × ℕ) (F E D : ℕ)
    (hF : selected.2 ≤ F) (hFirst : first.2 ≤ E) (hSecond : second.2 ≤ E) (hD : probability.2 ≤ D) :
    (collect prepared selected first second probability).2 ≤ F+2*E+D+24 := by
  change selected.2+first.2+second.2+probability.2+24 ≤ _
  omega

theorem terminal_work {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) (W : ℕ) (hW : 1 ≤ W)
    (hCap : ∀ j,width (prepared.capacity.read j) ≤ W) (hResource : ∀ j,width (state.resource.read j) ≤ W) :
    (terminal prepared state).2 ≤ terminalPrice W := by
  let selected := BinaryReflectedFocusMeasured.preparedFocus prepared state
  let pi := Equiv.swap selected.1.1 2
  let first := endpoint prepared.system state (pi 0)
  let second := endpoint prepared.system state (pi 1)
  let probability := BinaryQuadraticMeasured.apply .div (state.resource.read selected.1.1) (prepared.capacity.read selected.1.1)
  have hFocus := BinaryReflectedFocusMeasured.focus_work prepared.capacity state.resource W hW hCap hResource
  have hFirst := endpoint_work prepared.system state (pi 0) W (hResource (pi 0))
  have hSecond := endpoint_work prepared.system state (pi 1) W (hResource (pi 1))
  have hDiv := (BinaryReflectedSystemMeasured.opcode_bounds .div _ _ W (hResource selected.1.1) (hCap selected.1.1)).1
  have hResult := collect_work prepared selected first second probability _ _ _ hFocus hFirst hSecond hDiv
  rw [terminal_eq]
  simpa only [selected,pi,first,second,probability,terminalPrice] using hResult

theorem reached_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) :
    (terminal prepared result.state).2 ≤ terminalPrice (2*expressionHeightBudget s 21+1) ∧
      usage (terminal prepared result.state).1.2 ≤ BinaryReflectedTerminalInputLifetime.terminalEnvelope (2*expressionHeightBudget s 21+1) := by
  have hWidths := BinaryReflectedFocusLifetime.prepared_reached_widths input source hC hR hCase s hs hH N bits result hSuccess prepared
  refine ⟨terminal_work prepared result.state _ (by omega) hWidths.1 hWidths.2,?_⟩
  rw [terminal_erases]
  exact BinaryReflectedTerminalInputLifetime.reached_usage input source hC hR hCase s hs hH N bits result hSuccess prepared

theorem reached_all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (borrowed steps : ℕ) :
    retainedHeap borrowed (terminal prepared result.state).1.2 steps ≤
      borrowed+BinaryReflectedTerminalInputLifetime.terminalEnvelope (2*expressionHeightBudget s 21+1) ∧
    framePeak ((terminal prepared result.state).1.2.take steps) ≤
      BinaryReflectedTerminalInputLifetime.terminalEnvelope (2*expressionHeightBudget s 21+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (reached_bounds input source hC hR hCase s hs hH N bits result hSuccess prepared).2 borrowed steps

end Blotto.BinaryReflectedTerminalInputMeasured
