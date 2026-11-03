import Blotto.BinaryReflectedFallbackHeight
import Blotto.BinaryCategoricalLowerFallbackWork

/-! The deterministic reflected fallback retains one lower resource result,
one prepared terminal input/permutation and one full nested table. Lower
categorical choice and selected interpolation/reflection reuse that table.
Exact original fallback bytes and source-derived primitive prices are proved.
Pre-resource setup and complete computational-model costs remain separate. -/

namespace Blotto.BinaryReflectedFallbackFactory
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup

structure Prepared (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer : Fin K → Bool) where
  table : BinaryStoredOverlapEnvironment.Segment 3 18
  canonical : table.Canonical
  nonnegative : ∀ slot, 0 ≤ value (table.weight.read slot)
  table_correct : table = BinaryTerminalFallback.table input hC K outer
  resourceWork : ℕ
  terminalInputWork : ℕ
  factoryWork : ℕ

def prepareFromState (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (resourceWork : ℕ)
    (K : ℕ) (outer : Fin K → Bool) : Prepared input hC hAd K outer :=
  let assembled := BinaryNestedTerminalPreparationWork.prepareWithWork (prepare input) state.state
  let factory := BinaryNestedSpecFactoryWork.profileWithWork assembled.1.1 K outer
  let table : BinaryStoredOverlapEnvironment.Segment 3 18 := BinaryTerminalProfileCompiler.permute factory.1 assembled.1.2
  have hTable : table = BinaryTerminalFallback.table input hC K outer := by
    unfold table
    rw [BinaryNestedSpecFactoryWork.profileWithWork_state,BinaryNestedTerminalPreparationWork.prepareWithWork_state,hState]
    rfl
  ⟨table,(by rw [hTable]; exact BinaryTerminalFallback.table_canonical input hC K outer),
    (by rw [hTable]; exact BinaryTerminalFallback.table_nonnegative input hC hAd K outer),hTable,
    resourceWork,assembled.2,factory.2⟩

def prepareTerminal (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer : Fin K → Bool) : Prepared input hC hAd K outer :=
  let resource := BinaryThreeResourceFallbackWork.setupWithCharge input hC
  prepareFromState input hC hAd resource.1 (BinaryThreeResourceFallbackWork.setupWithCharge_state input hC)
    resource.2.booleanWork K outer

def Prepared.slotWithWork {input : BinaryFourParameters.Input} {hC : input.Canonical}
    {hAd : BinaryTerminalFallback.Admissible input} {K : ℕ} {outer : Fin K → Bool}
    (prepared : Prepared input hC hAd K outer) : Fin 18 × ℕ :=
  BinaryCategoricalLowerFallbackWork.segmentWithWork prepared.table prepared.canonical prepared.nonnegative 0

theorem Prepared.slotWithWork_state {input : BinaryFourParameters.Input} {hC : input.Canonical}
    {hAd : BinaryTerminalFallback.Admissible input} {K : ℕ} {outer : Fin K → Bool}
    (prepared : Prepared input hC hAd K outer) :
    prepared.slotWithWork.1 = BinaryTerminalFallback.slot input hC hAd K outer := by
  unfold Prepared.slotWithWork
  rw [BinaryCategoricalLowerFallbackWork.segmentWithWork_state]
  cases prepared with
  | mk table canonical nonnegative table_correct resourceWork terminalInputWork factoryWork =>
      cases table_correct
      rfl

def selectionBound (s K : ℕ) : ℕ := BinaryCategoricalLowerFallbackWork.bound 18 (expressionHeightBudget (max s (K + 2)) 68)

theorem Prepared.slotWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer : Fin K → Bool) (prepared : Prepared input hC hAd K outer) :
    prepared.slotWithWork.2 ≤ selectionBound s K := by
  have hRef : prepared.table.Refines ((BinaryTerminalFallback.terminal input source hC hR hCase).profile K outer) := by
    rw [prepared.table_correct]
    exact BinaryTerminalFallback.table_refines input source hC hR hCase K outer
  have hHeight := BinaryReflectedFallbackHeight.profile_height input source hC hR hCase s hs hH K outer
  exact BinaryCategoricalLowerFallbackWork.segmentWithWork_bound _ _ _ _ hRef _ hHeight.1 0

theorem prepareTerminal_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer : Fin K → Bool) :
    let prepared := prepareTerminal input hC hAd K outer
    prepared.resourceWork ≤ BinaryThreeResourceFallbackWork.bound s ∧
      prepared.terminalInputWork ≤ BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) ∧
      prepared.factoryWork ≤ BinaryReflectedFactoryPrepared.bound s K := by
  have hResource := BinaryThreeResourceFallbackWork.setupWithCharge_bound input source hC hR hCase s hs hH
  have hInput := BinaryReflectedFallbackHeight.terminal_input_bound input source hC hR hCase s hs hH
  have hFactory := BinaryReflectedFallbackHeight.factory_bound input source hC hR hCase s hs hH K outer
  dsimp only [prepareTerminal,prepareFromState]
  rw [BinaryThreeResourceFallbackWork.setupWithCharge_state]
  exact ⟨hResource,hInput,hFactory⟩

structure Ledger where
  resource : ℕ
  terminalInput : ℕ
  factory : ℕ
  selection : ℕ
  emission : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.resource + ledger.terminalInput + ledger.factory + ledger.selection + ledger.emission

def sampleWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool) :
    FixedArrayTable 4 SignedWord × Ledger :=
  let prepared := prepareTerminal input hC hAd K outer
  let selected := prepared.slotWithWork
  let emitted := BinaryReflectedSelectedEmissionWork.sampleWithWork input prepared.table selected.1 K scalar
  (emitted.1,⟨prepared.resourceWork,prepared.terminalInputWork,prepared.factoryWork,selected.2,emitted.2⟩)

theorem sampleWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool) :
    (sampleWithWork input hC hAd K outer scalar).1 = BinaryTerminalFallback.sample input hC hAd K outer scalar := by
  unfold sampleWithWork
  dsimp only
  rw [BinaryReflectedSelectedEmissionWork.sampleWithWork_state,Prepared.slotWithWork_state,
    (prepareTerminal input hC hAd K outer).table_correct]
  rfl

def bound (s K : ℕ) : ℕ := BinaryThreeResourceFallbackWork.bound s +
  BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) + BinaryReflectedFactoryPrepared.bound s K +
    selectionBound s K + BinaryReflectedSelectedEmissionWork.bound s K

theorem sampleWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (sampleWithWork input hC hAd K outer scalar).2.recorded ≤ bound s K := by
  let prepared := prepareTerminal input hC hAd K outer
  obtain ⟨hResource,hInput,hFactory⟩ := prepareTerminal_bounds input source hC hR hCase hAd s hs hH K outer
  have hSelection := Prepared.slotWithWork_bound input source hC hR hCase hAd s hs hH K outer prepared
  have hEmission : (BinaryReflectedSelectedEmissionWork.sampleWithWork input prepared.table prepared.slotWithWork.1 K scalar).2 ≤
      BinaryReflectedSelectedEmissionWork.bound s K := by
    rw [prepared.table_correct]
    exact BinaryReflectedFallbackHeight.selected_emission_bound input source hC hR hCase s hs hH K outer scalar _
  change prepared.resourceWork + prepared.terminalInputWork + prepared.factoryWork + prepared.slotWithWork.2 +
    (BinaryReflectedSelectedEmissionWork.sampleWithWork input prepared.table prepared.slotWithWork.1 K scalar).2 ≤ _
  change prepared.resourceWork ≤ _ at hResource
  change prepared.terminalInputWork ≤ _ at hInput
  change prepared.factoryWork ≤ _ at hFactory
  unfold bound
  omega

theorem sampleWithWork_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool) :
    ∀ j, CanonicalWord ((sampleWithWork input hC hAd K outer scalar).1.read j) := by
  rw [sampleWithWork_state]
  exact BinaryTerminalFallback.sample_canonical input hC hAd K outer scalar

theorem sampleWithWork_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (K : ℕ) (outer scalar : Fin K → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sampleWithWork input hC hAd K outer scalar).1.read j) : ℝ)) := by
  rw [sampleWithWork_state]
  exact BinaryTerminalFallback.sample_fullBudget input source hC hAd hR hCase K outer scalar

end Blotto.BinaryReflectedFallbackFactory
