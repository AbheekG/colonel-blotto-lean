import Blotto.BinaryReflectedFocusLifetime
import Blotto.BinaryLifetimeUsage

/-! The reached reflected state and retained capacity build the six nested
terminal words and coordinate permutation with traced endpoint scans and
focused division. -/
namespace Blotto.BinaryReflectedTerminalInputLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

def endpointWithTrace (system : BinaryReflectedFourSetup.System)
    (state : BinaryThreeResourceState.State) (j : Fin 3) : SignedWord × Trace :=
  let nonzero := BinaryBooleanPrimitiveLifetime.scanWithTrace (state.resource.read j).numerator
  (if nonzero.1 then system.short.read j else system.long.read j,wrap 8 2 [nonzero.2])

theorem endpointWithTrace_erasure (system : BinaryReflectedFourSetup.System)
    (state : BinaryThreeResourceState.State) (j : Fin 3) :
    (endpointWithTrace system state j).1 = BinaryNestedTerminalInput.endpoint system state j := by
  simp only [endpointWithTrace,BinaryNestedTerminalInput.endpoint,
    BinaryBooleanPrimitiveLifetime.scanWithTrace_erases]
  cases h : BinaryEuclideanGCD.nonzero (state.resource.read j).numerator <;> simp [h]

def endpointEnvelope (W : ℕ) : ℕ := 5 * (W + 1) + 16

theorem endpointWithTrace_usage (system : BinaryReflectedFourSetup.System)
    (state : BinaryThreeResourceState.State) (j : Fin 3) (W : ℕ)
    (hW : width (state.resource.read j) ≤ W) :
    usage (endpointWithTrace system state j).2 ≤ endpointEnvelope W := by
  have hScan := BinaryBooleanPrimitiveLifetime.scanWithTrace_bounds (state.resource.read j).numerator
  have hLen : (state.resource.read j).numerator.length ≤ W := by
    unfold width at hW
    omega
  have hw := wrap_usage 8 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace
    (state.resource.read j).numerator).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 8 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace
    (state.resource.read j).numerator).2]) ≤ _
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells endpointEnvelope at *
  omega

def terminalWithTrace {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) :
    (BinaryNestedParameters.Input × Equiv.Perm (Fin 3)) × Trace :=
  let selected := BinaryReflectedFocusLifetime.preparedFocusWithTrace prepared state
  let pi := Equiv.swap selected.1 2
  let first := endpointWithTrace prepared.system state (pi 0)
  let second := endpointWithTrace prepared.system state (pi 1)
  let probability := BinaryQuadraticLifetime.applyWithTrace .div
    (state.resource.read selected.1) (prepared.capacity.read selected.1)
  ((⟨prepared.system.M,first.1,second.1,prepared.system.long.read selected.1,
      prepared.system.short.read selected.1,probability.1⟩,pi),
    wrap 40 3 [selected.2,first.2,second.2,probability.2])

theorem terminalWithTrace_erasure {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State)
    (hState : ∀ j, CanonicalWord (state.resource.read j)) :
    (terminalWithTrace prepared state).1 =
      (BinaryNestedTerminalInput.prepare (BinaryReflectedFourSetup.prepare input) state,
        BinaryNestedTerminalInput.permutation (BinaryReflectedFourSetup.prepare input) state) := by
  unfold terminalWithTrace
  dsimp only
  rw [BinaryReflectedFocusLifetime.preparedFocusWithTrace_erasure]
  simp only [endpointWithTrace_erasure]
  rw [BinaryQuadraticLifetime.applyWithTrace_state .div _ _
    (hState _).1 (prepared.capacity_canonical _).1]
  rw [prepared.capacity_source,prepared.system_correct]
  rfl

def terminalEnvelope (W : ℕ) : ℕ :=
  BinaryReflectedFocusLifetime.focusEnvelope W + 2 * endpointEnvelope W + opcodeEnvelope W + 64

theorem terminalWithTrace_usage {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) (W : ℕ) (hW : 1 ≤ W)
    (hCap : ∀ j, width (prepared.capacity.read j) ≤ W)
    (hResource : ∀ j, width (state.resource.read j) ≤ W) :
    usage (terminalWithTrace prepared state).2 ≤ terminalEnvelope W := by
  let selected := BinaryReflectedFocusLifetime.preparedFocusWithTrace prepared state
  let pi := Equiv.swap selected.1 2
  let first := endpointWithTrace prepared.system state (pi 0)
  let second := endpointWithTrace prepared.system state (pi 1)
  let probability := BinaryQuadraticLifetime.applyWithTrace .div
    (state.resource.read selected.1) (prepared.capacity.read selected.1)
  have hFocus := BinaryReflectedFocusLifetime.focusWithTrace_usage prepared.capacity state.resource W hW hCap hResource
  have hFirst := endpointWithTrace_usage prepared.system state (pi 0) W (hResource (pi 0))
  have hSecond := endpointWithTrace_usage prepared.system state (pi 1) W (hResource (pi 1))
  have hProb := opcode_usage .div _ _ W (hResource selected.1) (hCap selected.1)
  have hw := wrap_usage 40 3 [selected.2,first.2,second.2,probability.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 40 3 [selected.2,first.2,second.2,probability.2]) ≤ _
  change usage selected.2 ≤ _ at hFocus
  change usage first.2 ≤ _ at hFirst
  change usage second.2 ≤ _ at hSecond
  change usage probability.2 ≤ _ at hProb
  unfold terminalEnvelope
  omega

theorem reached_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) :
    usage (terminalWithTrace prepared result.state).2 ≤
      terminalEnvelope (2 * expressionHeightBudget s 21 + 1) := by
  have hWidths := BinaryReflectedFocusLifetime.prepared_reached_widths input source hC hR hCase
    s hs hH N bits result hSuccess prepared
  exact terminalWithTrace_usage prepared result.state _ (by omega) hWidths.1 hWidths.2

theorem reached_all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (borrowed steps : ℕ) :
    retainedHeap borrowed (terminalWithTrace prepared result.state).2 steps ≤
      borrowed + terminalEnvelope (2 * expressionHeightBudget s 21 + 1) ∧
    framePeak ((terminalWithTrace prepared result.state).2.take steps) ≤
      terminalEnvelope (2 * expressionHeightBudget s 21 + 1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (reached_usage input source hC hR hCase s hs hH N bits result hSuccess prepared) borrowed steps

end Blotto.BinaryReflectedTerminalInputLifetime
