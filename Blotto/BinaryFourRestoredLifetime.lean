import Blotto.BinaryScalarTape
import Blotto.BinaryFourOrderedLifetime
import Blotto.RationalFourSpecHeight

/-! Three traced comparisons produce the ordered input and inverse permutation.
The complete selected ordered draw consumes that actual input; a successful
four-word row is restored by actual array construction, without fallback. -/
namespace Blotto.BinaryFourRestoredLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryFourSpecSampler.Input
abbrev Ordered := BinaryFourParameters.Input × Equiv.Perm (Fin 4)

def afterOrderWithTrace (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (ordered : Ordered)
    (hOrdered : ordered = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (orderTrace : Trace) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.Result store × Trace :=
  have hOrderedC : ordered.1.Canonical := by
    rw [hOrdered]
    exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1 := by
    rw [hOrdered]
    exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  let drawn := BinaryFourOrderedLifetime.runWithTrace store ordered.1 hOrderedC hOrderedAd K outer scalar pc hp
  match drawn.1.1 with
  | none => ((none,drawn.1.2),wrap 32 2 [orderTrace,drawn.2])
  | some row =>
      let restored := BinaryNestedResidualLifetime.copyWithTrace 4 (fun j => row.read (ordered.2 j))
      ((some restored.1,drawn.1.2),wrap 40 3 [orderTrace,drawn.2,restored.2])

theorem afterOrderWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (ordered : Ordered)
    (hOrdered : ordered = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (orderTrace : Trace) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithTrace store input hC hAd ordered hOrdered orderTrace K outer scalar pc hp).1 =
      BinaryPRGWordControllerFour.restoredRun store input hC hAd K outer scalar pc hp := by
  subst ordered
  unfold afterOrderWithTrace BinaryPRGWordControllerFour.restoredRun
  dsimp only
  rw [← BinaryFourOrderedLifetime.runWithTrace_erasure]
  cases h : (BinaryFourOrderedLifetime.runWithTrace store (BinaryFourSpecSampler.orderedInput input)
      (BinaryFourSpecSampler.orderedInput_canonical input hC)
      (BinaryFourSpecSampler.orderedInput_admissible input hC hAd) K outer scalar pc hp).1.1 with
  | none => rfl
  | some row =>
      simp only [BinaryNestedResidualLifetime.copyWithTrace_erasure]
      rfl

theorem afterOrderWithTrace_usage (store : BinarySeedLookupTree.Store) (input : Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (ordered : Ordered)
    (hOrdered : ordered = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (orderTrace : Trace) (C : ℕ) (hTrace : usage orderTrace ≤ C)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (afterOrderWithTrace store input hC hAd ordered hOrdered orderTrace K outer scalar pc hp).2 ≤
      C + BinaryFourOrderedLifetime.envelope s K store.width store.cap.value (store.cap.value-pc.value) + 512 := by
  subst ordered
  let drawn := BinaryFourOrderedLifetime.runWithTrace store (BinaryFourSpecSampler.orderedInput input)
    (BinaryFourSpecSampler.orderedInput_canonical input hC)
    (BinaryFourSpecSampler.orderedInput_admissible input hC hAd) K outer scalar pc hp
  have hDraw := BinaryFourOrderedLifetime.runWithTrace_usage store _ source.input
    (BinaryFourSpecSampler.orderedInput_canonical input hC)
    (BinaryFourSpecSampler.orderedInput_refines input source hC hR)
    (BinaryFourSpecSampler.orderedInput_admissible input hC hAd) s hs hH.input K outer scalar pc hp
  change usage drawn.2 ≤ _ at hDraw
  unfold afterOrderWithTrace
  dsimp only
  split
  · have hw := wrap_usage 32 2 [orderTrace,drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [orderTrace,drawn.2]) ≤ _
    omega
  · rename_i row hRow
    have hRestored := BinaryNestedResidualLifetime.copyWithTrace_usage 4
      (fun j => row.read (BinaryFourSpecSampler.permutation input j))
    have hw := wrap_usage 40 3 [orderTrace,drawn.2,
      (BinaryNestedResidualLifetime.copyWithTrace 4 (fun j => row.read (BinaryFourSpecSampler.permutation input j))).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 40 3 [orderTrace,drawn.2,
      (BinaryNestedResidualLifetime.copyWithTrace 4 (fun j => row.read (BinaryFourSpecSampler.permutation input j))).2]) ≤ _
    unfold BinaryNestedResidualLifetime.copyEnvelope at hRestored
    omega

def runWithTrace (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.Result store × Trace :=
  let ordered := BinaryFourOrderLifetime.orderedWithTrace input
  afterOrderWithTrace store input hC hAd ordered.1 (BinaryFourOrderLifetime.orderedWithTrace_erasure input)
    ordered.2 K outer scalar pc hp

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerFour.restoredRun store input hC hAd K outer scalar pc hp :=
  afterOrderWithTrace_erasure store input hC hAd (BinaryFourOrderLifetime.orderedWithTrace input).1
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input)
    (BinaryFourOrderLifetime.orderedWithTrace input).2 K outer scalar pc hp

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ∧
      (runWithTrace store input hC hAd K outer scalar pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerFour.restoredRun_position store input hC hAd K outer scalar pc hp

theorem runWithTrace_decoded (store : BinarySeedLookupTree.Store) (input : Input)
    (hC : input.Canonical) (hAd : BinaryFourSpecSampler.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.decoded store (runWithTrace store input hC hAd K outer scalar pc hp).1 =
      BinaryFourSpecPartialRun.runIndexed input hC hAd K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerFour.restoredRun_state store input hC hAd K outer scalar pc hp

def envelope (s K indexWidth seedCap remaining : ℕ) : ℕ :=
  BinaryFourOrderLifetime.orderedEnvelope s + BinaryFourOrderedLifetime.envelope s K indexWidth seedCap remaining + 512

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input hC hAd K outer scalar pc hp).2 ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) := by
  have hLength : ∀ j,RationalHeight (value (input.length.read j)) s := by
    intro j
    rw [hR.2.1 j]
    exact hH.2.1 j
  have hOrder := BinaryFourOrderLifetime.orderedWithTrace_usage input hC s hLength
  exact afterOrderWithTrace_usage store input source hC hR hAd s hs hH
    (BinaryFourOrderLifetime.orderedWithTrace input).1 (BinaryFourOrderLifetime.orderedWithTrace_erasure input)
    (BinaryFourOrderLifetime.orderedWithTrace input).2 (BinaryFourOrderLifetime.orderedEnvelope s)
    hOrder K outer scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : Input)
    (source : RationalFourSpec) (hC : input.Canonical) (hR : input.Refines source)
    (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input hC hAd K outer scalar pc hp).2 steps ≤
      borrowed + envelope s K store.width store.cap.value (store.cap.value-pc.value) ∧
    framePeak ((runWithTrace store input hC hAd K outer scalar pc hp).2.take steps) ≤
      envelope s K store.width store.cap.value (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input source hC hR hAd s hs hH K outer scalar pc hp) borrowed steps

end Blotto.BinaryFourRestoredLifetime
