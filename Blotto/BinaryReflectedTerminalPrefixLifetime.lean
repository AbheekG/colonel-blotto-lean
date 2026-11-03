import Blotto.BinaryReflectedTerminalInputLifetime
import Blotto.BinaryPRGWordControllerReflected

/-! The physical reflected resource result supplies its reached state and
retained setup directly to terminal input construction, with exhaustion. -/
namespace Blotto.BinaryReflectedTerminalPrefixLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Terminal := BinaryNestedParameters.Input × Equiv.Perm (Fin 3)

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    ((BinaryReflectedPreparationLifetime.Prepared input × Option Terminal) ×
      FixedBinaryWord store.width) × Trace :=
  let reached := BinaryPRGHeapReflectedLifetime.runWithTrace store input hC pc hp
  match reached.1.2.1 with
  | none => (((reached.1.1,none),reached.1.2.2),wrap 24 2 [reached.2])
  | some result =>
      let terminal := BinaryReflectedTerminalInputLifetime.terminalWithTrace reached.1.1 result.state
      (((reached.1.1,some terminal.1),reached.1.2.2),
        wrap 24 2 [reached.2,terminal.2])

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((runWithTrace store input hC pc hp).1.1.2,
      (runWithTrace store input hC pc hp).1.2) =
    ((BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1.map
      (fun result =>
        (BinaryNestedTerminalInput.prepare (BinaryReflectedFourSetup.prepare input) result.state,
          BinaryNestedTerminalInput.permutation (BinaryReflectedFourSetup.prepare input) result.state)),
      (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).2) := by
  let reached := BinaryPRGHeapReflectedLifetime.runWithTrace store input hC pc hp
  have hOld : reached.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp :=
    (BinaryPRGHeapReflectedLifetime.runWithTrace_erasure store input hC pc hp).trans
      (BinaryPRGHeapReflectedSetup.run_erasure store input hC pc hp)
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    have hOldNone := congrArg Prod.fst hOld
    rw [hNone] at hOldNone
    rw [← hOld]
    dsimp only [reached]
    simp only [hNone,Option.map_none]
  · rename_i result hSome
    have hTerminal := BinaryReflectedTerminalInputLifetime.terminalWithTrace_erasure reached.1.1
      result.state result.canonical
    rw [← hOld]
    dsimp only [reached] at hTerminal ⊢
    simp only [hSome,Option.map_some]
    exact congrArg (fun terminal : Terminal => (some terminal,reached.1.2.2)) hTerminal

theorem runWithTrace_position (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC pc hp).1.2.value ∧
      (runWithTrace store input hC pc hp).1.2.value ≤ store.cap.value := by
  have hCursor := congrArg Prod.snd (runWithTrace_erasure store input hC pc hp)
  change (runWithTrace store input hC pc hp).1.2 =
    (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).2 at hCursor
  rw [hCursor]
  exact BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp

def envelope (s indexWidth seedCap : ℕ) : ℕ :=
  BinaryPRGHeapReflectedLifetime.envelope s indexWidth seedCap +
    BinaryReflectedTerminalInputLifetime.terminalEnvelope (2 * expressionHeightBudget s 21 + 1) + 40

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store)
    (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC pc hp).2 ≤ envelope s store.width store.cap.value := by
  let reached := BinaryPRGHeapReflectedLifetime.runWithTrace store input hC pc hp
  have hPrefix := BinaryPRGHeapReflectedLifetime.runWithTrace_usage store input source hC hR
    hCase s hs hH pc hp
  change usage reached.2 ≤ _ at hPrefix
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [reached.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [reached.2]) ≤ _
    unfold envelope
    omega
  · rename_i result hSome
    have hOld : reached.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp :=
      (BinaryPRGHeapReflectedLifetime.runWithTrace_erasure store input hC pc hp).trans
        (BinaryPRGHeapReflectedSetup.run_erasure store input hC pc hp)
    have hOldSome : (BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp).1 = some result := by
      rw [← hOld]
      exact hSome
    have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result hOldSome
    have hTerminal := BinaryReflectedTerminalInputLifetime.reached_usage input source hC hR hCase
      s hs hH (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp)
      result hSuccess reached.1.1
    have hw := wrap_usage 24 2
      [reached.2,(BinaryReflectedTerminalInputLifetime.terminalWithTrace reached.1.1 result.state).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2
      [reached.2,(BinaryReflectedTerminalInputLifetime.terminalWithTrace reached.1.1 result.state).2]) ≤ _
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

end Blotto.BinaryReflectedTerminalPrefixLifetime
