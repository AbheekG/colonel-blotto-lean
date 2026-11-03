import Blotto.BinaryScalarTape
import Blotto.BinaryTerminalPermutationLifetime
import Blotto.BinaryReflectedTerminalInputLifetime
import Blotto.BinaryReflectedCategoricalWork

/-! A reached physical resource result and retained setup construct one actual
terminal table. Its sampler certificates are erased proofs; neither preparation
nor the complete profile is replayed to attach them. -/
namespace Blotto.BinaryReflectedTerminalFactoryLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def tableWithTrace {input : BinaryFourParameters.Input}
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (K : ℕ) (outer : BinaryScalarTape K) : Segment × Trace :=
  let terminal := BinaryReflectedTerminalInputLifetime.terminalWithTrace cached result.state
  let nested := BinaryNestedProfileLifetime.profileWithTrace terminal.1.1 K outer
  let restored := BinaryTerminalPermutationLifetime.permuteWithTrace nested.1 terminal.1.2
  (restored.1,wrap 40 3 [terminal.2,nested.2,restored.2])

theorem tableWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (K : ℕ) (outer : BinaryScalarTape K) :
    (tableWithTrace cached result K outer).1 =
      BinaryTerminalProfileCompiler.profile (BinaryReflectedFourSetup.prepare input) result.state K outer := by
  let terminal := BinaryReflectedTerminalInputLifetime.terminalWithTrace cached result.state
  have hTerminal := BinaryReflectedTerminalInputLifetime.terminalWithTrace_erasure cached result.state result.canonical
  change terminal.1 = _ at hTerminal
  have hInputC : terminal.1.1.Canonical := by
    rw [hTerminal]
    exact BinaryNestedTerminalInput.prepare_canonical _ _
      (BinaryReflectedFourSetup.prepare_canonical input hC) result.canonical
  have hNested := BinaryNestedProfileLifetime.profileWithTrace_erasure terminal.1.1 hInputC K outer
  unfold tableWithTrace BinaryTerminalProfileCompiler.profile
  dsimp only
  rw [BinaryTerminalPermutationLifetime.permuteWithTrace_erasure,hNested,hTerminal]

def preparedWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (K : ℕ) (outer : BinaryScalarTape K) : BinaryStoredSegmentProgram.Prepared 3 18 × Trace :=
  let table := tableWithTrace cached result K outer
  (⟨table.1,
    (by
      rw [tableWithTrace_erasure input hC]
      exact BinaryTerminalProfileCompiler.profile_canonical _ _
        (BinaryReflectedFourSetup.prepare_canonical input hC) result.canonical K outer),
    (by
      rw [tableWithTrace_erasure input hC]
      exact BinaryReflectedSerialRun.profile_nonnegative input hC hAd N bits result hSuccess K outer)⟩,table.2)

private theorem prepared_eq {p q : BinaryStoredSegmentProgram.Prepared 3 18}
    (h : p.table = q.table) : p = q := by
  cases p with
  | mk pt pc pn =>
    cases q with
    | mk qt qc qn =>
      dsimp only at h
      cases h
      rfl

theorem preparedWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (K : ℕ) (outer : BinaryScalarTape K) :
    (preparedWithTrace input hC hAd cached N bits result hSuccess K outer).1 =
      BinaryReflectedCategoricalWork.prepared input hC hAd N bits result hSuccess K outer := by
  apply prepared_eq
  change (tableWithTrace cached result K outer).1 =
    BinaryTerminalProfileCompiler.profile (BinaryReflectedFourSetup.prepare input) result.state K outer
  exact tableWithTrace_erasure input hC cached result K outer

def envelope (s K : ℕ) : ℕ :=
  BinaryReflectedTerminalInputLifetime.terminalEnvelope (2 * expressionHeightBudget s 21 + 1) +
    BinaryNestedProfileLifetime.envelope (expressionHeightBudget s 23) K + 6600 + 256

theorem tableWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K) :
    usage (tableWithTrace cached result K outer).2 ≤ envelope s K := by
  let terminal := BinaryReflectedTerminalInputLifetime.terminalWithTrace cached result.state
  let nested := BinaryNestedProfileLifetime.profileWithTrace terminal.1.1 K outer
  have hTerminal := BinaryReflectedTerminalInputLifetime.reached_usage input source hC hR hCase
    s hs hH N bits result hSuccess cached
  change usage terminal.2 ≤ _ at hTerminal
  have hTerminalState := BinaryReflectedTerminalInputLifetime.terminalWithTrace_erasure cached result.state result.canonical
  change terminal.1 = _ at hTerminalState
  have hInputC : terminal.1.1.Canonical := by
    rw [hTerminalState]
    exact BinaryNestedTerminalInput.prepare_canonical _ _
      (BinaryReflectedFourSetup.prepare_canonical input hC) result.canonical
  have hInputH : BinaryNestedParameterWork.InputHeight terminal.1.1 (expressionHeightBudget s 23) := by
    rw [hTerminalState]
    have h := BinaryNestedTerminalPreparationWork.reached_input_height input source hC hR hCase
      s hs hH N bits result hSuccess
    rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state] at h
    exact h
  have hs23 : 3 ≤ expressionHeightBudget s 23 := by unfold expressionHeightBudget; omega
  have hNested := BinaryNestedProfileLifetime.profileWithTrace_usage terminal.1.1 hInputC _ hs23 hInputH K outer
  change usage nested.2 ≤ _ at hNested
  have hPermuted := BinaryTerminalPermutationLifetime.permuteWithTrace_usage nested.1 terminal.1.2
  have hw := wrap_usage 40 3
    [terminal.2,nested.2,(BinaryTerminalPermutationLifetime.permuteWithTrace nested.1 terminal.1.2).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 40 3
    [terminal.2,nested.2,(BinaryTerminalPermutationLifetime.permuteWithTrace nested.1 terminal.1.2).2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (tableWithTrace cached result K outer).2 steps ≤ borrowed + envelope s K ∧
    framePeak ((tableWithTrace cached result K outer).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (tableWithTrace_usage input source hC hR hCase s hs hH N bits result hSuccess cached K outer) borrowed steps

end Blotto.BinaryReflectedTerminalFactoryLifetime
