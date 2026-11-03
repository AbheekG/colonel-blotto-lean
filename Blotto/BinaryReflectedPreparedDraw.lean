import Blotto.BinaryNestedTerminalPreparationWork
import Blotto.BinaryReflectedSelectedEmissionWork

/-! A reflected terminal prepares its native nested fields/permutation and one
complete profile table. Categorical selection and selected emission reuse that
same table. Exact old bytes, none and absolute position are retained. The
recorded draw price excludes the still-separate nested profile factory cost. -/

namespace Blotto.BinaryReflectedPreparedDraw
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun BinaryReflectedPhaseRefinement

structure Prepared (input : BinaryFourParameters.Input)
    (state : BinaryThreeResourceState.State) (K : ℕ) (outer : Fin K → Bool) where
  table : BinaryStoredOverlapEnvironment.Segment 3 18
  canonical : table.Canonical
  nonnegative : ∀ slot, 0 ≤ value (table.weight.read slot)
  table_correct : table = BinaryTerminalProfileCompiler.profile (prepare input) state K outer
  inputWork : ℕ

def prepareTerminal (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) : Prepared input result.state K outer :=
  let assembled := BinaryNestedTerminalPreparationWork.prepareWithWork (prepare input) result.state
  let table := BinaryTerminalProfileCompiler.permute (BinaryNestedSpecProfile.profile assembled.1.1 K outer) assembled.1.2
  have hTable : table = BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer := by
    unfold table
    rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state]
    rfl
  ⟨table, (by rw [hTable]; exact BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer),
    (by rw [hTable]; exact profile_nonnegative input hC hAd N bits result hSuccess K outer), hTable, assembled.2⟩

def Prepared.asSegment {input : BinaryFourParameters.Input}
    {state : BinaryThreeResourceState.State} {K : ℕ} {outer : Fin K → Bool}
    (prepared : Prepared input state K outer) : BinaryStoredSegmentProgram.Prepared 3 18 :=
  ⟨prepared.table,prepared.canonical,prepared.nonnegative⟩

def Prepared.runIndexedWithWork {input : BinaryFourParameters.Input}
    {state : BinaryThreeResourceState.State} {K : ℕ} {outer : Fin K → Bool}
    (prepared : Prepared input state K outer) (N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) : (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  let selected := BinaryStoredSegmentChoiceWork.selectIndexedWork prepared.asSegment 0 N bits pos hp
  match selected.1.1 with
  | none => ((none,selected.1.2),selected.2)
  | some slot =>
      let row := BinaryReflectedSelectedEmissionWork.sampleWithWork input prepared.table slot K scalar
      ((some row.1,selected.1.2),selected.2 + row.2)

theorem Prepared.runIndexedWithWork_state {input : BinaryFourParameters.Input}
    {state : BinaryThreeResourceState.State} {K : ℕ} {outer : Fin K → Bool}
    (prepared : Prepared input state K outer) (N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    (prepared.runIndexedWithWork N scalar bits pos hp).1 =
      let selected := prepared.asSegment.selectIndexed 0 N bits pos hp
      (selected.1.map (fun slot => BinaryReflectedTerminalEmission.sample input state K outer scalar slot),selected.2) := by
  unfold runIndexedWithWork
  rw [← BinaryStoredSegmentChoiceWork.selectIndexedWork_state prepared.asSegment 0 N bits pos hp]
  dsimp only
  cases hs : (BinaryStoredSegmentChoiceWork.selectIndexedWork prepared.asSegment 0 N bits pos hp).1.1 with
  | none => rfl
  | some slot =>
    dsimp only
    rw [BinaryReflectedSelectedEmissionWork.sampleWithWork_state,prepared.table_correct]
    rfl

theorem Prepared.selectIndexed_state {input : BinaryFourParameters.Input} {state : BinaryThreeResourceState.State}
    {K : ℕ} {outer : Fin K → Bool} (prepared : Prepared input state K outer)
    (hC : (BinaryTerminalProfileCompiler.profile (prepare input) state K outer).Canonical)
    (hWeights : ∀ slot, 0 ≤ value ((BinaryTerminalProfileCompiler.profile (prepare input) state K outer).weight.read slot))
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    prepared.asSegment.selectIndexed 0 N bits pos hp = BinaryCategoricalRun.runIndexed 0 N bits
      (.remaining (NativeBinarySegmentSampler.weights (BinaryTerminalProfileCompiler.profile (prepare input) state K outer) hC hWeights)) pos hp := by
  cases prepared with
  | mk table canonical nonnegative table_correct inputWork =>
    cases table_correct
    rfl

def bound (s K remaining : ℕ) : ℕ := BinaryReflectedCategoricalWork.bound s K remaining +
  BinaryReflectedSelectedEmissionWork.bound s K

theorem Prepared.runIndexedWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer scalar : Fin K → Bool)
    (prepared : Prepared input result.state K outer) (pos : ℕ) (hp : pos ≤ N) :
    (prepared.runIndexedWithWork N scalar bits pos hp).2 ≤ bound s K (N - pos) := by
  let terminal := (source.reflectedResourceSystem hCase).terminalData (phaseResult input source hC hR hCase N bits result hSuccess)
  have hRef : prepared.table.Refines (terminal.profile K outer) := by
    rw [prepared.table_correct]
    exact terminal_profile_refines input source hC hR hCase N bits result hSuccess K outer
  have hHeight := BinaryReflectedReachedHeight.profile_height input source hC hR hCase s hs hH N bits result hSuccess K outer
  have hSelect := BinaryStoredSegmentChoiceWork.selectIndexedWork_bound prepared.asSegment (terminal.profile K outer) hRef
    _ hHeight.1 0 N bits pos hp
  unfold Prepared.runIndexedWithWork
  dsimp only
  cases he : (BinaryStoredSegmentChoiceWork.selectIndexedWork prepared.asSegment 0 N bits pos hp).1.1 with
  | none =>
    dsimp only
    exact hSelect.trans (Nat.le_add_right _ _)
  | some slot =>
    dsimp only
    have hEmit : (BinaryReflectedSelectedEmissionWork.sampleWithWork input prepared.table slot K scalar).2 ≤
        BinaryReflectedSelectedEmissionWork.bound s K := by
      rw [prepared.table_correct]
      exact BinaryReflectedSelectedEmissionWork.reached_bound input source hC hR hCase s hs hH N bits result hSuccess K outer scalar slot
    exact Nat.add_le_add hSelect hEmit

theorem prepareTerminal_inputWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (prepareTerminal input hC hAd N bits result hSuccess K outer).inputWork ≤
      BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) :=
  BinaryNestedTerminalPreparationWork.reached_bound input source hC hR hCase s hs hH N bits result hSuccess

end Blotto.BinaryReflectedPreparedDraw
