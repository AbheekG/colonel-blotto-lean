import Blotto.BinaryReflectedBoundaryPrefixLifetime
import Blotto.BinaryNestedSelectedRegimePrefixLifetime

/-! The reached reflected terminal executes boundary dispatch and,
for an interior input, sorts endpoints, retains one parameter table and chooses
the first, second or third ordered regime by actual traced comparisons. -/
namespace Blotto.BinaryReflectedRegimePrefixLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Terminal := BinaryReflectedTerminalPrefixLifetime.Terminal
abbrev Result := BinaryNestedSelectedRegimePrefixLifetime.Result

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    ((BinaryReflectedPreparationLifetime.Prepared input × Option (Terminal × Result)) ×
      FixedBinaryWord store.width) × Trace :=
  let prior := BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp
  match prior.1.1.2 with
  | none => (((prior.1.1.1,none),prior.1.2),wrap 24 2 [prior.2])
  | some terminal =>
      let interior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace terminal.1
      (((prior.1.1.1,some (terminal,interior.1)),prior.1.2),
        wrap 24 2 [prior.2,interior.2])

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
          (terminal,BinaryNestedSelectedRegimePrefixLifetime.oldResult terminal.1)) := by
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
      (makeTerminal result,BinaryNestedSelectedRegimePrefixLifetime.oldResult (makeTerminal result).1)) =
      (old.1.map makeTerminal).map
        (fun terminal => (terminal,BinaryNestedSelectedRegimePrefixLifetime.oldResult terminal.1)) := by
    cases h : old.1 with
    | none => rfl
    | some result => rfl
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    change none = old.1.map (fun result =>
      (makeTerminal result,BinaryNestedSelectedRegimePrefixLifetime.oldResult (makeTerminal result).1))
    rw [hMap,← hOld,hNone]
    rfl
  · rename_i terminal hSome
    have hContract := BinaryReflectedBoundaryPrefixLifetime.reached_terminal_contract store input source
      hC hR hCase s hs hH pc hp terminal hSome
    change some (terminal,(BinaryNestedSelectedRegimePrefixLifetime.runWithTrace terminal.1).1) =
      old.1.map (fun result =>
        (makeTerminal result,BinaryNestedSelectedRegimePrefixLifetime.oldResult (makeTerminal result).1))
    rw [hMap,← hOld,hSome]
    simp only [Option.map_some,Option.some.injEq]
    rw [BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_erasure terminal.1 hContract.1]

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
    BinaryNestedSelectedRegimePrefixLifetime.envelope (expressionHeightBudget s 23) + 40

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC pc hp).2 ≤ envelope s store.width store.cap.value := by
  let prior := BinaryReflectedTerminalPrefixLifetime.runWithTrace store input hC pc hp
  have hPrior := BinaryReflectedTerminalPrefixLifetime.runWithTrace_usage store input source
    hC hR hCase s hs hH pc hp
  change usage prior.2 ≤ _ at hPrior
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [prior.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [prior.2]) ≤ _
    unfold envelope
    omega
  · rename_i terminal hSome
    have hContract := BinaryReflectedBoundaryPrefixLifetime.reached_terminal_contract store input source
      hC hR hCase s hs hH pc hp terminal hSome
    have hs' : 3 ≤ expressionHeightBudget s 23 := by
      unfold expressionHeightBudget
      omega
    have hInterior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_usage terminal.1
      hContract.1 _ hs' hContract.2
    have hw := wrap_usage 24 2
      [prior.2,(BinaryNestedSelectedRegimePrefixLifetime.runWithTrace terminal.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2
      [prior.2,(BinaryNestedSelectedRegimePrefixLifetime.runWithTrace terminal.1).2]) ≤ _
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

end Blotto.BinaryReflectedRegimePrefixLifetime
