import Blotto.BinaryScalarTape
import Blotto.BinaryReflectedLowerLifetime
import Blotto.BinaryReflectedTerminalFactoryLifetime
import Blotto.BinaryReflectedFallbackHeight

/-! The actual physically completed lower state/cache builds one terminal and
restored nested table. Fallback sampler proof fields attach to that produced
table; old resource/profile factories occur only in erased equality proofs. -/
namespace Blotto.BinaryReflectedLowerFactoryLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedFourSetup
set_option maxHeartbeats 2000000

def fromResourceWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (K : ℕ) (outer : BinaryScalarTape K) :
    BinaryStoredSegmentProgram.Prepared 3 18 × Trace :=
  let table := BinaryReflectedTerminalFactoryLifetime.tableWithTrace cached state K outer
  have hTable : table.1 = BinaryTerminalFallback.table input hC K outer := by
    rw [BinaryReflectedTerminalFactoryLifetime.tableWithTrace_erasure input hC,hState]
    rfl
  (⟨table.1,(by rw [hTable]; exact BinaryTerminalFallback.table_canonical input hC K outer),
    (by rw [hTable]; exact BinaryTerminalFallback.table_nonnegative input hC hAd K outer)⟩,table.2)

theorem fromResourceWithTrace_table (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (K : ℕ) (outer : BinaryScalarTape K) :
    (fromResourceWithTrace input hC hAd cached state hState K outer).1.table =
      BinaryTerminalFallback.table input hC K outer := by
  change (BinaryReflectedTerminalFactoryLifetime.tableWithTrace cached state K outer).1 = _
  rw [BinaryReflectedTerminalFactoryLifetime.tableWithTrace_erasure input hC,hState]
  rfl

theorem table_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K) :
    usage (BinaryReflectedTerminalFactoryLifetime.tableWithTrace cached (BinaryResourceFallback.setup input hC) K outer).2 ≤
      BinaryReflectedTerminalFactoryLifetime.envelope s K := by
  let result := BinaryResourceFallback.setup input hC
  let terminal := BinaryReflectedTerminalInputLifetime.terminalWithTrace cached result.state
  let nested := BinaryNestedProfileLifetime.profileWithTrace terminal.1.1 K outer
  have hCapWidth : ∀ j,width (cached.capacity.read j) ≤ 2*expressionHeightBudget s 21+1 := by
    intro j
    have hh : RationalHeight (value (cached.capacity.read j)) (expressionHeightBudget s 21) := by
      rw [cached.capacity_source]
      exact (BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH j).mono
        (expressionHeightBudget_mono s (by decide : 15 ≤ 21))
    have h := (cached.capacity_canonical j).2.trans (rationalWordWidth_of_height hh)
    omega
  have hResourceWidth : ∀ j,width (result.state.resource.read j) ≤ 2*expressionHeightBudget s 21+1 := by
    intro j
    have h := (result.canonical j).2.trans (rationalWordWidth_of_height
      (BinaryReflectedFallbackHeight.resource_height input source hC hR hCase s hs hH j))
    omega
  have hTerminal := BinaryReflectedTerminalInputLifetime.terminalWithTrace_usage cached result.state _
    (by omega) hCapWidth hResourceWidth
  change usage terminal.2 ≤ _ at hTerminal
  have hTerminalState := BinaryReflectedTerminalInputLifetime.terminalWithTrace_erasure cached result.state result.canonical
  change terminal.1 = _ at hTerminalState
  have hInputC : terminal.1.1.Canonical := by
    rw [hTerminalState]
    exact BinaryNestedTerminalInput.prepare_canonical _ _ (prepare_canonical input hC) result.canonical
  have hInputH : BinaryNestedParameterWork.InputHeight terminal.1.1 (expressionHeightBudget s 23) := by
    rw [hTerminalState]
    have h := BinaryReflectedFallbackHeight.input_height input source hC hR hCase s hs hH
    rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state] at h
    exact h
  have hs23 : 3 ≤ expressionHeightBudget s 23 := by unfold expressionHeightBudget; omega
  have hNested := BinaryNestedProfileLifetime.profileWithTrace_usage terminal.1.1 hInputC _ hs23 hInputH K outer
  change usage nested.2 ≤ _ at hNested
  have hPermuted := BinaryTerminalPermutationLifetime.permuteWithTrace_usage nested.1 terminal.1.2
  have hw := wrap_usage 40 3 [terminal.2,nested.2,
    (BinaryTerminalPermutationLifetime.permuteWithTrace nested.1 terminal.1.2).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 40 3 [terminal.2,nested.2,
    (BinaryTerminalPermutationLifetime.permuteWithTrace nested.1 terminal.1.2).2]) ≤ _
  unfold BinaryReflectedTerminalFactoryLifetime.envelope
  omega

theorem fromResourceWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (K : ℕ) (outer : BinaryScalarTape K) :
    usage (fromResourceWithTrace input hC hAd cached state hState K outer).2 ≤
      BinaryReflectedTerminalFactoryLifetime.envelope s K := by
  subst state
  exact table_usage input source hC hR hCase s hs hH cached K outer

def prepareWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer : BinaryScalarTape K) :
    BinaryStoredSegmentProgram.Prepared 3 18 × Trace :=
  let lower := BinaryReflectedLowerLifetime.runWithTrace input hC
  let factory := fromResourceWithTrace input hC hAd lower.1.1 lower.1.2
    (BinaryReflectedLowerLifetime.runWithTrace_erasure input hC) K outer
  (factory.1,wrap 32 2 [lower.2,factory.2])

theorem prepareWithTrace_table (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer : BinaryScalarTape K) :
    (prepareWithTrace input hC hAd K outer).1.table = BinaryTerminalFallback.table input hC K outer :=
  fromResourceWithTrace_table input hC hAd _ _
    (BinaryReflectedLowerLifetime.runWithTrace_erasure input hC) K outer

def envelope (s K : ℕ) : ℕ :=
  BinaryReflectedLowerLifetime.envelope s+BinaryReflectedTerminalFactoryLifetime.envelope s K+64

theorem prepareWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer : BinaryScalarTape K) :
    usage (prepareWithTrace input hC hAd K outer).2 ≤ envelope s K := by
  let lower := BinaryReflectedLowerLifetime.runWithTrace input hC
  let factory := fromResourceWithTrace input hC hAd lower.1.1 lower.1.2
    (BinaryReflectedLowerLifetime.runWithTrace_erasure input hC) K outer
  have hL := BinaryReflectedLowerLifetime.runWithTrace_usage input source hC hR hCase s hs hH
  have hF := fromResourceWithTrace_usage input source hC hR hCase hAd s hs hH lower.1.1 lower.1.2
    (BinaryReflectedLowerLifetime.runWithTrace_erasure input hC) K outer
  have hw := wrap_usage 32 2 [lower.2,factory.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (prepareWithTrace input hC hAd K outer).2 ≤ _ at hw
  change usage lower.2 ≤ _ at hL
  change usage factory.2 ≤ _ at hF
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace input hC hAd K outer).2 steps ≤ borrowed+envelope s K ∧
      framePeak ((prepareWithTrace input hC hAd K outer).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepareWithTrace_usage input source hC hR hCase hAd s hs hH K outer) borrowed steps

end Blotto.BinaryReflectedLowerFactoryLifetime
