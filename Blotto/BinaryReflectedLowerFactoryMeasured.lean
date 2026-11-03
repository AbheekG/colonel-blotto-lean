import Blotto.BinaryReflectedLowerMeasured
import Blotto.BinaryReflectedTerminalFactoryMeasured
import Blotto.BinaryReflectedLowerFactoryLifetime

/-! Deterministic lower completion feeds its returned state and cache to the
measured terminal/nested/permutation factory once. Erased fallback equalities
attach sampler certificates to that actual table. Source heights derive the
lower terminal bounds directly, without a successful random-run hypothesis. -/
namespace Blotto.BinaryReflectedLowerFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedFourSetup
set_option maxHeartbeats 1800000

def attach (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer : BinaryScalarTape K)
    (built : (BinaryReflectedTerminalFactoryMeasured.Segment × Trace) × ℕ)
    (hTable : built.1.1 = BinaryTerminalFallback.table input hC K outer) :
    (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ :=
  ((⟨built.1.1,(by rw [hTable]; exact BinaryTerminalFallback.table_canonical input hC K outer),
    (by rw [hTable]; exact BinaryTerminalFallback.table_nonnegative input hC hAd K outer)⟩,built.1.2),built.2)

def fromResource (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (K : ℕ) (outer : BinaryScalarTape K) :
    (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ :=
  let built := BinaryReflectedTerminalFactoryMeasured.table cached state K outer
  attach input hC hAd K outer built (by
    rw [BinaryReflectedTerminalFactoryMeasured.table_erasure input hC,hState]
    rfl)

theorem fromResource_table (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (K : ℕ) (outer : BinaryScalarTape K) :
    (fromResource input hC hAd cached state hState K outer).1.1.table = BinaryTerminalFallback.table input hC K outer := by
  change (BinaryReflectedTerminalFactoryMeasured.table cached state K outer).1.1 = _
  rw [BinaryReflectedTerminalFactoryMeasured.table_erasure input hC,hState]
  rfl

theorem fromResource_data (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (K : ℕ) (outer : BinaryScalarTape K) :
    (fromResource input hC hAd cached state hState K outer).1.1 =
      (BinaryReflectedLowerFactoryLifetime.fromResourceWithTrace input hC hAd cached state hState K outer).1 := by
  apply BinaryReflectedTerminalFactoryMeasured.prepared_unique
  rw [fromResource_table,BinaryReflectedLowerFactoryLifetime.fromResourceWithTrace_table]

theorem table_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K) :
    (BinaryReflectedTerminalFactoryMeasured.table cached (BinaryResourceFallback.setup input hC) K outer).2 ≤
      BinaryReflectedTerminalFactoryMeasured.workEnvelope s K ∧
    usage (BinaryReflectedTerminalFactoryMeasured.table cached (BinaryResourceFallback.setup input hC) K outer).1.2 ≤
      BinaryReflectedTerminalFactoryMeasured.envelope s K := by
  let result := BinaryResourceFallback.setup input hC
  let terminal := BinaryReflectedTerminalInputMeasured.terminal cached result.state
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
  have hTerminalWork := BinaryReflectedTerminalInputMeasured.terminal_work cached result.state _
    (by omega) hCapWidth hResourceWidth
  have hTerminalUsage : usage terminal.1.2 ≤
      BinaryReflectedTerminalInputLifetime.terminalEnvelope (2*expressionHeightBudget s 21+1) := by
    dsimp only [terminal]
    rw [BinaryReflectedTerminalInputMeasured.terminal_erases]
    exact BinaryReflectedTerminalInputLifetime.terminalWithTrace_usage cached result.state _
      (by omega) hCapWidth hResourceWidth
  have hState := BinaryReflectedTerminalInputMeasured.terminal_source_data cached result.state result.canonical
  have hInputC : terminal.1.1.1.Canonical := by
    rw [hState]
    exact BinaryNestedTerminalInput.prepare_canonical _ _ (prepare_canonical input hC) result.canonical
  have hInputH : BinaryNestedParameterWork.InputHeight terminal.1.1.1 (expressionHeightBudget s 23) := by
    rw [hState]
    have h := BinaryReflectedFallbackHeight.input_height input source hC hR hCase s hs hH
    rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state] at h
    exact h
  have hResult := BinaryReflectedTerminalFactoryMeasured.fromTerminal_bounds terminal hInputC _
    (by unfold expressionHeightBudget; omega) hInputH K outer _ _ ⟨hTerminalWork,hTerminalUsage⟩
  simp only [BinaryReflectedTerminalFactoryMeasured.table_record]
  unfold BinaryReflectedTerminalFactoryMeasured.workEnvelope
    BinaryReflectedTerminalFactoryMeasured.envelope
  with_reducible exact hResult

theorem fromResource_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (K : ℕ) (outer : BinaryScalarTape K) :
    (fromResource input hC hAd cached state hState K outer).2 ≤ BinaryReflectedTerminalFactoryMeasured.workEnvelope s K ∧
      usage (fromResource input hC hAd cached state hState K outer).1.2 ≤ BinaryReflectedTerminalFactoryMeasured.envelope s K := by
  subst state
  exact table_bounds input source hC hR hCase s hs hH cached K outer

def collect {input : BinaryFourParameters.Input} (lower : ((BinaryReflectedPreparationLifetime.Prepared input ×
      BinaryThreeResourcePair.Certified (prepare input).capacity) × Trace) × ℕ)
    (factory : (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ) :
    (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ :=
  ((factory.1.1,wrap 32 2 [lower.1.2,factory.1.2]),lower.2+factory.2+8)

def prepared (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer : BinaryScalarTape K) :
    (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ :=
  let lower := BinaryReflectedLowerMeasured.run input hC
  let factory := fromResource input hC hAd lower.1.1.1 lower.1.1.2
    (BinaryReflectedLowerMeasured.run_state input hC) K outer
  collect lower factory

theorem prepared_table (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer : BinaryScalarTape K) :
    (prepared input hC hAd K outer).1.1.table = BinaryTerminalFallback.table input hC K outer :=
  fromResource_table input hC hAd _ _ (BinaryReflectedLowerMeasured.run_state input hC) K outer

theorem prepared_data (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer : BinaryScalarTape K) :
    (prepared input hC hAd K outer).1.1 =
      (BinaryReflectedLowerFactoryLifetime.prepareWithTrace input hC hAd K outer).1 := by
  apply BinaryReflectedTerminalFactoryMeasured.prepared_unique
  rw [prepared_table,BinaryReflectedLowerFactoryLifetime.prepareWithTrace_table]

def workEnvelope (s K : ℕ) : ℕ :=
  BinaryReflectedLowerMeasured.workEnvelope s+BinaryReflectedTerminalFactoryMeasured.workEnvelope s K+8

def envelope (s K : ℕ) : ℕ :=
  BinaryReflectedLowerMeasured.envelope s+BinaryReflectedTerminalFactoryMeasured.envelope s K+64

theorem collect_bounds {input : BinaryFourParameters.Input} (lower : ((BinaryReflectedPreparationLifetime.Prepared input ×
      BinaryThreeResourcePair.Certified (prepare input).capacity) × Trace) × ℕ)
    (factory : (BinaryStoredSegmentProgram.Prepared 3 18 × Trace) × ℕ) (L F U V : ℕ)
    (hL : lower.2 ≤ L ∧ usage lower.1.2 ≤ U) (hF : factory.2 ≤ F ∧ usage factory.1.2 ≤ V) :
    (collect lower factory).2 ≤ L+F+8 ∧ usage (collect lower factory).1.2 ≤ U+V+64 := by
  have hw := wrap_usage 32 2 [lower.1.2,factory.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change lower.2+factory.2+8 ≤ _ ∧ usage (wrap 32 2 [lower.1.2,factory.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem prepared_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer : BinaryScalarTape K) :
    (prepared input hC hAd K outer).2 ≤ workEnvelope s K ∧ usage (prepared input hC hAd K outer).1.2 ≤ envelope s K := by
  let lower := BinaryReflectedLowerMeasured.run input hC
  let factory := fromResource input hC hAd lower.1.1.1 lower.1.1.2
    (BinaryReflectedLowerMeasured.run_state input hC) K outer
  have hL := BinaryReflectedLowerMeasured.run_bounds input source hC hR hCase s hs hH
  have hF := fromResource_bounds input source hC hR hCase hAd s hs hH lower.1.1.1 lower.1.1.2
    (BinaryReflectedLowerMeasured.run_state input hC) K outer
  have hResult := collect_bounds lower factory _ _ _ _ hL hF
  unfold prepared workEnvelope envelope
  with_reducible exact hResult

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepared input hC hAd K outer).1.2 steps ≤ borrowed+envelope s K ∧
      framePeak ((prepared input hC hAd K outer).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepared_bounds input source hC hR hCase hAd s hs hH K outer).2 borrowed steps

end Blotto.BinaryReflectedLowerFactoryMeasured
