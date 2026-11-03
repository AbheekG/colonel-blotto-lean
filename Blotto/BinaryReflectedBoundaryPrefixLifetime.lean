import Blotto.BinaryReflectedTerminalPrefixLifetime
import Blotto.BinaryNestedBoundaryLifetime

/-! The reached reflected terminal executes the nested q=0/q=1 descriptor
branches and retains their 18-slot arrays. An interior input remains tagged
as a reached terminal with no boundary descriptor. -/
namespace Blotto.BinaryReflectedBoundaryPrefixLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Terminal := BinaryReflectedTerminalPrefixLifetime.Terminal
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    ((BinaryReflectedPreparationLifetime.Prepared input × Option (Terminal × Option Segment)) ×
      FixedBinaryWord store.width) × Trace :=
  let prior := BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp
  match prior.1.1.2 with
  | none => (((prior.1.1.1,none),prior.1.2),wrap 24 2 [prior.2])
  | some terminal =>
      let boundary := BinaryNestedBoundaryLifetime.boundaryWithTrace terminal.1
      (((prior.1.1.1,some (terminal,boundary.1)),prior.1.2),
        wrap 24 2 [prior.2,boundary.2])

theorem reached_terminal_contract (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (terminal : Terminal)
    (hSome : (BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp).1.1.2 =
      some terminal) :
    terminal.1.Canonical ∧
      BinaryNestedParameterWork.InputHeight terminal.1 (expressionHeightBudget s 23) := by
  have hOld := congrArg Prod.fst
    (BinaryReflectedTerminalPrefixLifetime.runWithTrace_erasure store input hC pc hp)
  change (BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp).1.1.2 =
    (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1.map
      (fun result =>
        (BinaryNestedTerminalInput.prepare (BinaryReflectedFourSetup.prepare input) result.state,
          BinaryNestedTerminalInput.permutation (BinaryReflectedFourSetup.prepare input) result.state)) at hOld
  rw [hSome] at hOld
  cases hResult : (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 with
  | none => simp [hResult] at hOld
  | some result =>
      have hTerminal : terminal =
          (BinaryNestedTerminalInput.prepare (BinaryReflectedFourSetup.prepare input) result.state,
            BinaryNestedTerminalInput.permutation (BinaryReflectedFourSetup.prepare input) result.state) := by
        simpa only [hResult,Option.map_some,Option.some.injEq] using hOld
      have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp
        result hResult
      have hHeight := BinaryNestedTerminalPreparationWork.reached_input_height input source
        hC hR hCase s hs hH (store.cap.value-pc.value)
        (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess
      rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state] at hHeight
      rw [hTerminal]
      exact ⟨BinaryNestedTerminalInput.prepare_canonical _ _
        (BinaryReflectedFourSetup.prepare_canonical input hC) result.canonical,hHeight⟩

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC pc hp).1.1.2 =
      (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1.map
        (fun result =>
          let terminal :=
            (BinaryNestedTerminalInput.prepare (BinaryReflectedFourSetup.prepare input) result.state,
              BinaryNestedTerminalInput.permutation (BinaryReflectedFourSetup.prepare input) result.state)
          (terminal,BinaryNestedBoundaryLifetime.oldBoundary terminal.1)) := by
  let prior := BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp
  have hOld := congrArg Prod.fst
    (BinaryReflectedTerminalPrefixLifetime.runWithTrace_erasure store input hC pc hp)
  let old := BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp
  let makeTerminal := fun
      (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity) =>
    (BinaryNestedTerminalInput.prepare (BinaryReflectedFourSetup.prepare input) result.state,
      BinaryNestedTerminalInput.permutation (BinaryReflectedFourSetup.prepare input) result.state)
  change prior.1.1.2 = old.1.map makeTerminal at hOld
  have hMap : old.1.map (fun result =>
      (makeTerminal result,BinaryNestedBoundaryLifetime.oldBoundary (makeTerminal result).1)) =
      (old.1.map makeTerminal).map
        (fun terminal => (terminal,BinaryNestedBoundaryLifetime.oldBoundary terminal.1)) := by
    cases h : old.1 with
    | none => rfl
    | some result => rfl
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    change none = _
    change none = old.1.map (fun result =>
      (makeTerminal result,BinaryNestedBoundaryLifetime.oldBoundary (makeTerminal result).1))
    rw [hMap,← hOld,hNone]
    rfl
  · rename_i terminal hSome
    have hContract := reached_terminal_contract store input source hC hR hCase s hs hH pc hp terminal hSome
    change some (terminal,(BinaryNestedBoundaryLifetime.boundaryWithTrace terminal.1).1) =
      old.1.map (fun result =>
        (makeTerminal result,BinaryNestedBoundaryLifetime.oldBoundary (makeTerminal result).1))
    rw [hMap,← hOld,hSome]
    simp only [Option.map_some,Option.some.injEq]
    rw [BinaryNestedBoundaryLifetime.boundaryWithTrace_erasure terminal.1 hContract.1]

theorem runWithTrace_cursor (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC pc hp).1.2 =
      (BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp).1.2 := by
  unfold runWithTrace
  dsimp only
  split <;> rfl

theorem runWithTrace_position (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC pc hp).1.2.value ∧
      (runWithTrace store input hC pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_cursor]
  exact BinaryReflectedTerminalPrefixLifetime.runWithTrace_position store input hC pc hp

def envelope (s indexWidth seedCap : ℕ) : ℕ :=
  BinaryReflectedTerminalPrefixLifetime.envelope s indexWidth seedCap +
    BinaryNestedBoundaryLifetime.envelope (expressionHeightBudget s 23) + 40

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC pc hp).2 ≤ envelope s store.width store.cap.value := by
  let prior := BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp
  have hPrefix := BinaryReflectedTerminalPrefixLifetime.runWithTrace_usage store input source
    hC hR hCase s hs hH pc hp
  change usage prior.2 ≤ _ at hPrefix
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [prior.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [prior.2]) ≤ _
    unfold envelope
    omega
  · rename_i terminal hSome
    have hContract := reached_terminal_contract store input source hC hR hCase s hs hH pc hp terminal hSome
    have hs' : 3 ≤ expressionHeightBudget s 23 := by
      unfold expressionHeightBudget
      omega
    have hBoundary := BinaryNestedBoundaryLifetime.boundaryWithTrace_usage terminal.1
      hContract.1 _ hs' hContract.2
    have hw := wrap_usage 24 2
      [prior.2,(BinaryNestedBoundaryLifetime.boundaryWithTrace terminal.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2
      [prior.2,(BinaryNestedBoundaryLifetime.boundaryWithTrace terminal.1).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC pc hp).2 steps ≤
      borrowed + envelope s store.width store.cap.value ∧
    framePeak ((runWithTrace store input hC pc hp).2.take steps) ≤
      envelope s store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hCase s hs hH pc hp) borrowed steps

end Blotto.BinaryReflectedBoundaryPrefixLifetime
