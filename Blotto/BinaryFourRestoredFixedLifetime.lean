import Blotto.BinaryScalarTape
import Blotto.BinaryFourOrderedFixedLifetime
import Blotto.BinaryFourOrderLifetime
import Blotto.BinaryFourSpecFixed
import Blotto.RationalFourSpecHeight

/-! Actual sorting feeds the complete ordered fixed draw; inverse four-word
restoration applies to every returned row, including both exhaustion fallbacks.
Original unsorted fields derive the whole retained every-prefix reservation. -/
namespace Blotto.BinaryFourRestoredFixedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000
abbrev Input := BinaryFourSpecSampler.Input
abbrev Ordered := BinaryFourParameters.Input × Equiv.Perm (Fin 4)

def afterOrderWithTrace (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (orderTrace : Trace) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace :=
  have hOrderedC : ordered.1.Canonical := by
    rw [hOrdered]
    exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1 := by
    rw [hOrdered]
    exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  let drawn := BinaryFourOrderedFixedLifetime.runWithTrace store ordered.1 hOrderedC hOrderedAd K outer scalar pc hp
  let restored := BinaryNestedResidualLifetime.copyWithTrace 4 (fun j => drawn.1.1.read (ordered.2 j))
  ((restored.1,drawn.1.2),wrap 40 3 [orderTrace,drawn.2,restored.2])

theorem afterOrderWithTrace_window (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (orderTrace : Trace) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithTrace store input hC hAd ordered hOrdered orderTrace K outer scalar pc hp).1.1 =
      BinaryFourSpecFixed.sample input hC hAd K (store.cap.value-pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) := by
  subst ordered
  unfold afterOrderWithTrace
  dsimp only
  rw [BinaryNestedResidualLifetime.copyWithTrace_erasure,BinaryFourOrderedFixedLifetime.runWithTrace_window]
  rfl

theorem afterOrderWithTrace_position (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (orderTrace : Trace) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (afterOrderWithTrace store input hC hAd ordered hOrdered orderTrace K outer scalar pc hp).1.2.value ∧
      (afterOrderWithTrace store input hC hAd ordered hOrdered orderTrace K outer scalar pc hp).1.2.value ≤ store.cap.value := by
  subst ordered
  exact BinaryFourOrderedFixedLifetime.runWithTrace_position store (BinaryFourSpecSampler.orderedInput input)
    (BinaryFourSpecSampler.orderedInput_canonical input hC) (BinaryFourSpecSampler.orderedInput_admissible input hC hAd)
    K outer scalar pc hp

theorem afterOrderWithTrace_cursor (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (orderTrace : Trace) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithTrace store input hC hAd ordered hOrdered orderTrace K outer scalar pc hp).1.2 =
      (BinaryPRGWordControllerFour.restoredRun store input hC hAd K outer scalar pc hp).2 := by
  subst ordered
  exact BinaryFourOrderedFixedLifetime.runWithTrace_cursor store (BinaryFourSpecSampler.orderedInput input)
    (BinaryFourSpecSampler.orderedInput_canonical input hC) (BinaryFourSpecSampler.orderedInput_admissible input hC hAd)
    K outer scalar pc hp

theorem afterOrderWithTrace_usage (store : BinarySeedLookupTree.Store) (input : Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourSpecSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (ordered : Ordered)
    (hOrdered : ordered = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (orderTrace : Trace) (C : ℕ) (hTrace : usage orderTrace ≤ C)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (afterOrderWithTrace store input hC hAd ordered hOrdered orderTrace K outer scalar pc hp).2 ≤
      C+BinaryFourOrderedFixedLifetime.envelope s K store.width store.cap.value (store.cap.value-pc.value)+512 := by
  subst ordered
  let drawn := BinaryFourOrderedFixedLifetime.runWithTrace store (BinaryFourSpecSampler.orderedInput input)
    (BinaryFourSpecSampler.orderedInput_canonical input hC) (BinaryFourSpecSampler.orderedInput_admissible input hC hAd)
    K outer scalar pc hp
  let restored := BinaryNestedResidualLifetime.copyWithTrace 4 (fun j => drawn.1.1.read (BinaryFourSpecSampler.permutation input j))
  have hDraw := BinaryFourOrderedFixedLifetime.runWithTrace_usage store _ source.input
    (BinaryFourSpecSampler.orderedInput_canonical input hC) (BinaryFourSpecSampler.orderedInput_refines input source hC hR)
    (BinaryFourSpecSampler.orderedInput_admissible input hC hAd) s hs hH.input K outer scalar pc hp
  have hRestore := BinaryNestedResidualLifetime.copyWithTrace_usage 4
    (fun j => drawn.1.1.read (BinaryFourSpecSampler.permutation input j))
  have hw := wrap_usage 40 3 [orderTrace,drawn.2,restored.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (afterOrderWithTrace store input hC hAd
    (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input) rfl
    orderTrace K outer scalar pc hp).2 ≤ _ at hw
  change usage drawn.2 ≤ _ at hDraw
  change usage restored.2 ≤ _ at hRestore
  unfold BinaryNestedResidualLifetime.copyEnvelope at hRestore
  omega

def runWithTrace (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace :=
  let ordered := BinaryFourOrderLifetime.orderedWithTrace input
  afterOrderWithTrace store input hC hAd ordered.1 (BinaryFourOrderLifetime.orderedWithTrace_erasure input)
    ordered.2 K outer scalar pc hp

theorem runWithTrace_window (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1.1 =
      BinaryFourSpecFixed.sample input hC hAd K (store.cap.value-pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) :=
  afterOrderWithTrace_window store input hC hAd (BinaryFourOrderLifetime.orderedWithTrace input).1
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input) (BinaryFourOrderLifetime.orderedWithTrace input).2 K outer scalar pc hp

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ≤ store.cap.value :=
  afterOrderWithTrace_position store input hC hAd (BinaryFourOrderLifetime.orderedWithTrace input).1
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input) (BinaryFourOrderLifetime.orderedWithTrace input).2 K outer scalar pc hp

theorem runWithTrace_cursor (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1.2 =
      (BinaryPRGWordControllerFour.restoredRun store input hC hAd K outer scalar pc hp).2 :=
  afterOrderWithTrace_cursor store input hC hAd (BinaryFourOrderLifetime.orderedWithTrace input).1
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input) (BinaryFourOrderLifetime.orderedWithTrace input).2 K outer scalar pc hp

def envelope (s K i b remaining : ℕ) : ℕ :=
  BinaryFourOrderLifetime.orderedEnvelope s+BinaryFourOrderedFixedLifetime.envelope s K i b remaining+512

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourSpecSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K outer scalar pc hp).2 ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  have hLengths : ∀ j,RationalHeight (value (input.length.read j)) s := by
    intro j
    rw [hR.2.1 j]
    exact hH.2.1 j
  exact afterOrderWithTrace_usage store input source hC hR hAd s hs hH
    (BinaryFourOrderLifetime.orderedWithTrace input).1 (BinaryFourOrderLifetime.orderedWithTrace_erasure input)
    (BinaryFourOrderLifetime.orderedWithTrace input).2 _ (BinaryFourOrderLifetime.orderedWithTrace_usage input hC s hLengths)
    K outer scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourSpecSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K outer scalar pc hp).2 steps ≤
      borrowed+envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
      framePeak ((runWithTrace store input hC hAd K outer scalar pc hp).2.take steps) ≤
        envelope s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store input source hC hR hAd s hs hH K outer scalar pc hp) borrowed steps

theorem runWithTrace_canonical (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ∀ j,CanonicalWord ((runWithTrace store input hC hAd K outer scalar pc hp).1.1.read j) := by
  rw [runWithTrace_window]
  exact BinaryFourSpecFixed.sample_canonical input hC hAd K _ outer scalar _

theorem runWithTrace_fullBudget (store : BinarySeedLookupTree.Store) (input : Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    FullBudget (source.B : ℝ)
      (fun j => (value ((runWithTrace store input hC hAd K outer scalar pc hp).1.1.read j) : ℝ)) := by
  rw [runWithTrace_window]
  have hRow : (fun j => (value ((BinaryFourSpecFixed.sample input hC hAd K (store.cap.value-pc.value) outer scalar
      (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
        (store.cap.value-pc.value) (by omega))).read j) : ℝ)) =
      fun j => (source.fixedSample K (store.cap.value-pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) j : ℝ) := by
    funext j
    rw [BinaryFourSpecFixed.sample_value input source hC hR hAd]
  rw [hRow]
  exact source.fixedSample_fullBudget K _ outer scalar _

end Blotto.BinaryFourRestoredFixedLifetime
