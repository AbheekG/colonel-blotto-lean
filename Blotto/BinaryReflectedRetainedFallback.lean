import Blotto.BinaryReflectedRetainedFactoryRun
import Blotto.BinaryReflectedFallbackFactory

/-! Deterministic fallback consumes the same retained setup/parameter/capacity
cache as the random reflected path. One lower result, terminal input and full
table are retained for choice/emission. Complete original row/budget semantics
and source-derived suffix prices hold; cold construction charges prefix once. -/

namespace Blotto.BinaryReflectedRetainedFallback
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup

def prepareFromState (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (state : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hState : state = BinaryResourceFallback.setup input hC) (resourceWork : ℕ) (K : ℕ) (outer : Fin K → Bool) :
    BinaryReflectedFallbackFactory.Prepared input hC hAd K outer :=
  let assembled := BinaryReflectedCachedTerminalInput.Prepared.terminalWithWork cached state.state
  let factory := BinaryNestedSpecFactoryWork.profileWithWork assembled.1.1 K outer
  let table := BinaryTerminalProfileCompiler.permute factory.1 assembled.1.2
  have hTable : table = BinaryTerminalFallback.table input hC K outer := by
    unfold table
    rw [BinaryNestedSpecFactoryWork.profileWithWork_state,BinaryReflectedCachedTerminalInput.terminalWithWork_original,hState]
    rfl
  ⟨table,(by rw [hTable]; exact BinaryTerminalFallback.table_canonical input hC K outer),
    (by rw [hTable]; exact BinaryTerminalFallback.table_nonnegative input hC hAd K outer),hTable,
    resourceWork,assembled.2,factory.2⟩

def prepareTerminal (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedSetupCache.Prepared input) (K : ℕ) (outer : Fin K → Bool) :
    BinaryReflectedFallbackFactory.Prepared input hC hAd K outer :=
  let resource := BinaryReflectedCachedCertifiedResult.lowerWithCharge cached
  prepareFromState input hC hAd cached resource.1 (BinaryReflectedCachedCertifiedResult.lowerWithCharge_state input hC cached)
    resource.2.booleanWork K outer

theorem prepareTerminal_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer : Fin K → Bool) :
    let prepared := prepareTerminal input hC hAd cached K outer
    prepared.resourceWork ≤ BinaryThreeResourceFallbackWork.bound s ∧
      prepared.terminalInputWork ≤ BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) ∧
      prepared.factoryWork ≤ BinaryReflectedFactoryPrepared.bound s K := by
  have hResource := BinaryReflectedCachedCertifiedResult.lowerWithCharge_bound input source hC hR hCase s hs hH cached
  have hInput := BinaryReflectedFallbackHeight.terminal_input_bound input source hC hR hCase s hs hH
  have hFactory := BinaryReflectedFallbackHeight.factory_bound input source hC hR hCase s hs hH K outer
  have hPrice := BinaryReflectedCachedTerminalInput.terminalWithWork_prefix_price cached (BinaryResourceFallback.setup input hC).state
  rw [cached.system_correct] at hPrice
  have hFields := (BinaryReflectedCachedTerminalInput.terminalWithWork_original cached (BinaryResourceFallback.setup input hC).state).trans
    (BinaryNestedTerminalPreparationWork.prepareWithWork_state (prepare input) (BinaryResourceFallback.setup input hC).state).symm
  dsimp only [prepareTerminal,prepareFromState]
  rw [BinaryReflectedCachedCertifiedResult.lowerWithCharge_state input hC cached]
  constructor
  · exact hResource
  constructor
  · omega
  · rw [hFields]
    exact hFactory

def sampleWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (K : ℕ) (outer scalar : Fin K → Bool) : FixedArrayTable 4 SignedWord × BinaryReflectedFallbackFactory.Ledger :=
  let prepared := prepareTerminal input hC hAd cached K outer
  let selected := prepared.slotWithWork
  let emitted := BinaryReflectedSelectedEmissionWork.sampleWithWork input prepared.table selected.1 K scalar
  (emitted.1,⟨prepared.resourceWork,prepared.terminalInputWork,prepared.factoryWork,selected.2,emitted.2⟩)

theorem sampleWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    (sampleWithWork input hC hAd cached K outer scalar).1 = BinaryTerminalFallback.sample input hC hAd K outer scalar := by
  unfold sampleWithWork
  dsimp only
  rw [BinaryReflectedSelectedEmissionWork.sampleWithWork_state,BinaryReflectedFallbackFactory.Prepared.slotWithWork_state,
    (prepareTerminal input hC hAd cached K outer).table_correct]
  rfl

theorem sampleWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : Fin K → Bool) :
    (sampleWithWork input hC hAd cached K outer scalar).2.recorded ≤ BinaryReflectedFallbackFactory.bound s K := by
  let prepared := prepareTerminal input hC hAd cached K outer
  obtain ⟨hResource,hInput,hFactory⟩ := prepareTerminal_bounds input source hC hR hCase hAd cached s hs hH K outer
  have hSelection := BinaryReflectedFallbackFactory.Prepared.slotWithWork_bound input source hC hR hCase hAd s hs hH K outer prepared
  have hEmission : (BinaryReflectedSelectedEmissionWork.sampleWithWork input prepared.table prepared.slotWithWork.1 K scalar).2 ≤
      BinaryReflectedSelectedEmissionWork.bound s K := by
    rw [prepared.table_correct]
    exact BinaryReflectedFallbackHeight.selected_emission_bound input source hC hR hCase s hs hH K outer scalar _
  change prepared.resourceWork ≤ _ at hResource
  change prepared.terminalInputWork ≤ _ at hInput
  change prepared.factoryWork ≤ _ at hFactory
  change prepared.resourceWork + prepared.terminalInputWork + prepared.factoryWork + prepared.slotWithWork.2 +
    (BinaryReflectedSelectedEmissionWork.sampleWithWork input prepared.table prepared.slotWithWork.1 K scalar).2 ≤ _
  unfold BinaryReflectedFallbackFactory.bound
  omega

theorem sampleWithWork_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : BinaryTerminalFallback.Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sampleWithWork input hC hAd cached K outer scalar).1.read j) : ℝ)) := by
  rw [sampleWithWork_state]
  exact BinaryTerminalFallback.sample_fullBudget input source hC hAd hR hCase K outer scalar

end Blotto.BinaryReflectedRetainedFallback
