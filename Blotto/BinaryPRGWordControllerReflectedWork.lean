import Blotto.BinaryPRGWordControllerReflectedSetupWork
import Blotto.BinaryPRGWordControllerWork
import Blotto.BinaryReflectedFactoryPrepared

/-! Reached primitive work for the actual reflected controller.  A selected
emission rebuilds the original profile; both productions are charged.  The
categorical branch uses its concrete quadratic Boolean preparation and Store
counter.  Emission retains its actual original arithmetic backend.  Fixed
table/control visits are additional; full address/compiler interpretation is
not inferred from this source component ledger. -/

namespace Blotto.BinaryPRGWordControllerReflectedWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryReflectedFourSetup BinarySharedResourceRun BinaryReflectedSerialRun
open BinaryReflectedPhaseRefinement

def profileWithWork (input : BinaryFourParameters.Input) (state : BinaryThreeResourceState.State)
    (K : ℕ) (outer : Fin K → Bool) : BinaryStoredOverlapEnvironment.Segment 3 18 × ℕ :=
  let setup := BinaryReflectedSetupWork.prepareWithWork input
  let assembled := BinaryNestedTerminalPreparationWork.prepareWithWork setup.1 state
  let factory := BinaryNestedSpecFactoryWork.profileWithWork assembled.1.1 K outer
  (BinaryTerminalProfileCompiler.permute factory.1 assembled.1.2,
    setup.2 + assembled.2 + factory.2 + 216)

theorem profileWithWork_state (input : BinaryFourParameters.Input) (state : BinaryThreeResourceState.State)
    (K : ℕ) (outer : Fin K → Bool) :
    (profileWithWork input state K outer).1 = BinaryTerminalProfileCompiler.profile (prepare input) state K outer := by
  unfold profileWithWork BinaryTerminalProfileCompiler.profile
  dsimp only
  rw [BinaryNestedSpecFactoryWork.profileWithWork_state, BinaryNestedTerminalPreparationWork.prepareWithWork_state,
    BinaryReflectedSetupWork.prepareWithWork_state]

def profileBound (s K : ℕ) : ℕ := BinaryReflectedSetupWork.bound s +
  BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) +
    BinaryReflectedFactoryPrepared.bound s K + 216

theorem profileWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (profileWithWork input result.state K outer).2 ≤ profileBound s K := by
  have hSetup := BinaryReflectedSetupWork.prepareWithWork_bound input source hC hR s hs hH
  have hAssembly := BinaryNestedTerminalPreparationWork.reached_bound input source hC hR hCase s hs hH
    N bits result hSuccess
  have hFactory := BinaryReflectedFactoryPrepared.prepareTerminal_factoryWork_bound input source hC hR hCase hAd
    s hs hH N bits result hSuccess K outer
  change (BinaryNestedSpecFactoryWork.profileWithWork
    (BinaryNestedTerminalPreparationWork.prepareWithWork (prepare input) result.state).1.1 K outer).2 ≤ _ at hFactory
  unfold profileWithWork profileBound
  dsimp only
  rw [BinaryReflectedSetupWork.prepareWithWork_state]
  omega

theorem categorical_bound {n k : ℕ} (store : Store)
    (prepared : BinaryStoredSegmentProgram.Prepared n k) (source : RationalSegmentLottery n k)
    (hR : prepared.table.Refines source) (s : ℕ)
    (hWeight : ∀ slot, RationalHeight (source.weight slot) s)
    (fallback : Fin k) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerCategorical.run store fallback
      (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp).2 ≤
      BinaryPRGWordControllerWork.selectionBound k s store.width (store.cap.value - pc.value) := by
  let weights := NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative
  have hRun := BinaryPRGWordControllerCategorical.run_bound (BinaryStoredSegmentChoiceWork.denominator prepared.table)
    (BinaryStoredSegmentChoiceWork.denominator_positive prepared.table) store fallback weights
    (BinaryStoredSegmentChoiceWork.source_unit prepared source hR) pc hp
  have hWidth := BinaryStoredSegmentChoiceWork.denominator_width prepared.table s
    (fun slot => by rw [hR.1 slot]; exact hWeight slot)
  have hPosition := BinaryPRGWordControllerCategorical.run_position_bounds store fallback weights pc hp
  have hSpan := Nat.sub_le_sub_right hPosition.2 pc.value
  apply hRun.trans
  have hLength : weights.items.length = k := List.length_ofFn
  rw [hLength]
  unfold BinaryPRGWordControllerCategorical.bound BinaryPRGWordControllerCategorical.choiceBound
    BinaryPRGWordControllerPreparation.preparationBound BinaryPRGWordControllerCategorical.bodyBound
    BinaryPRGWordControllerWork.selectionBound BinaryWordIndexCoinController.allowance
  dsimp only
  gcongr

def select (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerReflected.Selection store input × ℕ :=
  let reached := BinaryPRGWordControllerReflectedSetupWork.run store input hC pc hp
  match hResult : reached.1.1 with
  | none => ((none, reached.1.2), reached.2 + 2)
  | some result =>
      have hReached : (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 = some result :=
        (congrArg Prod.fst (BinaryPRGWordControllerReflectedSetupWork.run_erasure store input hC pc hp)).symm.trans hResult
      let table := profileWithWork input result.state K outer
      have hTable := profileWithWork_state input result.state K outer
      have hTableC : table.1.Canonical := by
        rw [hTable]
        exact BinaryTerminalProfileCompiler.profile_canonical
          _ result.state (prepare_canonical input hC) result.canonical K outer
      have hNonnegative : ∀ slot, 0 ≤ value (table.1.weight.read slot) := by
        rw [hTable]
        exact profile_nonnegative input hC hAd (store.cap.value - pc.value)
          (BinaryPRGWordControllerReflected.localReader store pc hp) result
          (BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result hReached) K outer
      have hPosition : reached.1.2.value ≤ store.cap.value := by
        rw [BinaryPRGWordControllerReflectedSetupWork.run_erasure]
        exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2
      let selected := BinaryPRGWordControllerCategorical.run store (0 : Fin 18)
        (NativeBinarySegmentSampler.weights table.1 hTableC hNonnegative) reached.1.2 hPosition
      ((selected.1.1.map (fun slot => (result, slot)), selected.1.2),
        reached.2 + table.2 + selected.2 + 56)

set_option maxHeartbeats 1000000 in
theorem select_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (select store input hC hAd K outer pc hp).1 = BinaryPRGWordControllerReflected.select store input hC hAd K outer pc hp := by
  have hErasure := BinaryPRGWordControllerReflectedSetupWork.run_erasure store input hC pc hp
  have hOption := congrArg Prod.fst hErasure
  have hPC := congrArg Prod.snd hErasure
  unfold select BinaryPRGWordControllerReflected.select
  dsimp only
  split
  · rename_i hNone
    have hOld := hOption.symm.trans hNone
    split
    · exact congrArg (fun p => (none, p)) hPC
    · rename_i other hOther
      cases hOld.symm.trans hOther
  · rename_i result hSome
    have hOld := hOption.symm.trans hSome
    split
    · rename_i hNone
      cases hOld.symm.trans hNone
    · rename_i other hOther
      have he : result = other := Option.some.inj (hOld.symm.trans hOther)
      subst other
      simp only [profileWithWork_state, BinaryPRGWordControllerDataCategorical.run_erasure, hPC]

def selectionBound (s K indexWidth remaining : ℕ) : ℕ :=
  BinaryPRGWordControllerReflectedSetupWork.bound s indexWidth remaining + profileBound s K +
    BinaryPRGWordControllerWork.selectionBound 18 (expressionHeightBudget (max s (K + 2)) 68) indexWidth remaining + 56

theorem select_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (select store input hC hAd K outer pc hp).2 ≤ selectionBound s K store.width (store.cap.value - pc.value) := by
  have hPrefix := BinaryPRGWordControllerReflectedSetupWork.run_bound store input source hC hR hCase s hs hH pc hp
  unfold select
  dsimp only
  split
  · unfold selectionBound; omega
  · rename_i result hResult
    have hReached : (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 = some result :=
      (congrArg Prod.fst (BinaryPRGWordControllerReflectedSetupWork.run_erasure store input hC pc hp)).symm.trans hResult
    have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result hReached
    let N := store.cap.value - pc.value
    let bits := BinaryPRGWordControllerReflected.localReader store pc hp
    have hProfile := profileWithWork_bound input source hC hR hCase hAd s hs hH N bits result hSuccess K outer
    let table := (profileWithWork input result.state K outer).1
    have hTable := profileWithWork_state input result.state K outer
    have hTableC : table.Canonical := by
      dsimp only [table]
      rw [hTable]
      exact BinaryTerminalProfileCompiler.profile_canonical
        _ result.state (prepare_canonical input hC) result.canonical K outer
    have hNonnegative : ∀ slot, 0 ≤ value (table.weight.read slot) := by
      dsimp only [table]
      rw [hTable]; exact profile_nonnegative input hC hAd N bits result hSuccess K outer
    let prepared : BinaryStoredSegmentProgram.Prepared 3 18 := ⟨table, hTableC, hNonnegative⟩
    let terminal := (source.reflectedResourceSystem hCase).terminalData (phaseResult input source hC hR hCase N bits result hSuccess)
    have hRef : table.Refines (terminal.profile K outer) := by
      dsimp only [table]
      rw [hTable]; exact terminal_profile_refines input source hC hR hCase N bits result hSuccess K outer
    have hHeight := BinaryReflectedReachedHeight.profile_height input source hC hR hCase s hs hH N bits result hSuccess K outer
    have hPosition := BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp
    rw [← BinaryPRGWordControllerReflectedSetupWork.run_erasure] at hPosition
    have hSelect := categorical_bound store prepared (terminal.profile K outer) hRef _ hHeight.1 0
      (BinaryPRGWordControllerReflectedSetupWork.run store input hC pc hp).1.2 hPosition.2
    have hRemaining : store.cap.value - (BinaryPRGWordControllerReflectedSetupWork.run store input hC pc hp).1.2.value ≤
        store.cap.value - pc.value := Nat.sub_le_sub_left hPosition.1 _
    have hSelect' : (BinaryPRGWordControllerCategorical.run store (0 : Fin 18)
      (NativeBinarySegmentSampler.weights table hTableC hNonnegative)
      (BinaryPRGWordControllerReflectedSetupWork.run store input hC pc hp).1.2 hPosition.2).2 ≤
      BinaryPRGWordControllerWork.selectionBound 18 (expressionHeightBudget (max s (K + 2)) 68)
        store.width (store.cap.value - pc.value) := hSelect.trans (by
      unfold BinaryPRGWordControllerWork.selectionBound
      dsimp only
      gcongr)
    change (BinaryPRGWordControllerCategorical.run store (0 : Fin 18)
      (NativeBinarySegmentSampler.weights table hTableC hNonnegative)
      (BinaryPRGWordControllerReflectedSetupWork.run store input hC pc hp).1.2 hPosition.2).2 ≤
      BinaryPRGWordControllerWork.selectionBound 18 (expressionHeightBudget (max s (K + 2)) 68)
        store.width (store.cap.value - pc.value) at hSelect'
    dsimp only [table] at hSelect'
    unfold selectionBound
    dsimp only
    omega

def emissionWithWork (input : BinaryFourParameters.Input) (state : BinaryThreeResourceState.State)
    (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) : FixedArrayTable 4 SignedWord × ℕ :=
  let table := profileWithWork input state K outer
  let row := BinaryReflectedSelectedEmissionWork.sampleWithWork input table.1 slot K scalar
  (row.1, table.2 + row.2 + 20)

theorem emissionWithWork_erasure (input : BinaryFourParameters.Input) (state : BinaryThreeResourceState.State)
    (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    (emissionWithWork input state K outer scalar slot).1 =
      BinaryReflectedTerminalEmission.sample input state K outer scalar slot := by
  unfold emissionWithWork BinaryReflectedTerminalEmission.sample
  dsimp only
  rw [BinaryReflectedSelectedEmissionWork.sampleWithWork_state, profileWithWork_state]

def emissionBound (s K : ℕ) : ℕ := profileBound s K + BinaryReflectedSelectedEmissionWork.bound s K + 20

theorem emissionWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result)
    (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    (emissionWithWork input result.state K outer scalar slot).2 ≤ emissionBound s K := by
  have hTable := profileWithWork_bound input source hC hR hCase hAd s hs hH N bits result hSuccess K outer
  have hRow := BinaryReflectedSelectedEmissionWork.reached_bound input source hC hR hCase s hs hH
    N bits result hSuccess K outer scalar slot
  unfold emissionWithWork emissionBound
  dsimp only
  rw [profileWithWork_state]
  omega

theorem select_origin (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity) (slot : Fin 18)
    (h : (select store input hC hAd K outer pc hp).1.1 = some (result, slot)) :
    (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 = some result := by
  rw [select_erasure] at h
  unfold BinaryPRGWordControllerReflected.select at h
  dsimp only at h
  split at h
  · cases h
  · rename_i reached hReached
    obtain ⟨chosen, hChosen, hPair⟩ := Option.map_eq_some_iff.mp h
    have hResult := congrArg Prod.fst hPair
    dsimp only at hResult
    subst result
    exact hReached

def run (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerReflected.Result store × ℕ :=
  let selected := select store input hC hAd K outer pc hp
  match selected.1.1 with
  | none => ((none, selected.1.2), selected.2 + 2)
  | some pair =>
      let emitted := emissionWithWork input pair.1.state K outer scalar pair.2
      ((some emitted.1, selected.1.2), selected.2 + emitted.2 + 2)

theorem run_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1 = BinaryPRGWordControllerReflected.run store input hC hAd K outer scalar pc hp := by
  unfold run BinaryPRGWordControllerReflected.run
  dsimp only
  rw [select_erasure]
  split
  · rename_i hNone
    simp only [hNone, Option.map_none]
  · rename_i pair hPair
    simp only [hPair, Option.map_some, emissionWithWork_erasure]

def bound (s K indexWidth remaining : ℕ) : ℕ := selectionBound s K indexWidth remaining + emissionBound s K + 2

theorem run_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤ bound s K store.width (store.cap.value - pc.value) := by
  have hSelect := select_bound store input source hC hR hCase hAd s hs hH K outer pc hp
  unfold run
  dsimp only
  split
  · unfold bound; omega
  · rename_i pair hPair
    have hReached := select_origin store input hC hAd K outer pc hp pair.1 pair.2 hPair
    have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp pair.1 hReached
    have hEmit := emissionWithWork_bound input source hC hR hCase hAd s hs hH
      (store.cap.value - pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp)
      pair.1 hSuccess K outer scalar pair.2
    unfold bound
    omega

end Blotto.BinaryPRGWordControllerReflectedWork
