import Blotto.BinaryFourOrderedFixedMeasured
import Blotto.BinaryFourOrderMeasured
import Blotto.BinaryFourRestoredFixedLifetime

/-! Actual measured sorting feeds the complete measured ordered fixed draw.
Every four-word row, including exhaustion fallback, is restored by measured
reference packing. Bounded-window output and the absolute cursor are preserved. -/
namespace Blotto.BinaryFourRestoredFixedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev Input := BinaryFourSpecSampler.Input
abbrev Ordered := ((BinaryFourParameters.Input × Equiv.Perm (Fin 4)) × Trace) × ℕ
abbrev Result (store : BinarySeedLookupTree.Store) := ((FixedArrayTable 4 SignedWord × FixedBinaryWord store.width) × Trace) × ℕ

def restore (store : BinarySeedLookupTree.Store) (ordered : Ordered) (drawn : Result store) : Result store :=
  let restored := BinaryThreeReferenceMeasured.references 4 (fun j => drawn.1.1.1.read (ordered.1.1.2 j))
  (((restored.1.1,drawn.1.1.2),wrap 40 3 [ordered.1.2,drawn.1.2,restored.1.2]),ordered.2+drawn.2+restored.2+12)

def afterOrder (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  let drawn := BinaryFourOrderedFixedMeasured.run store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  restore store ordered drawn

def run (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  let ordered := BinaryFourOrderMeasured.ordered input
  afterOrder store input hC hAd ordered ((congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input)) K outer scalar pc hp

theorem afterOrder_data (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrder store input hC hAd ordered hOrdered K outer scalar pc hp).1.1 =
      (BinaryFourRestoredFixedLifetime.afterOrderWithTrace store input hC hAd ordered.1.1 hOrdered ordered.1.2 K outer scalar pc hp).1 := by
  unfold afterOrder restore BinaryFourRestoredFixedLifetime.afterOrderWithTrace
  dsimp only
  rw [BinaryFourOrderedFixedMeasured.run_data]
  simp only [BinaryThreeReferenceMeasured.references_data,BinaryNestedResidualLifetime.copyWithTrace_erasure]

theorem run_window (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1.1 =
      BinaryFourSpecFixed.sample input hC hAd K (store.cap.value-pc.value) outer scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) := by
  unfold run
  rw [afterOrder_data]
  exact BinaryFourRestoredFixedLifetime.afterOrderWithTrace_window store input hC hAd _ _ _ K outer scalar pc hp

def workEnvelope (s K i cap : ℕ) : ℕ := BinaryFourOrderMeasured.workEnvelope s+BinaryFourOrderedFixedMeasured.workEnvelope s K i cap+1700

def envelope (s K i cap : ℕ) : ℕ := BinaryFourOrderLifetime.orderedEnvelope s+BinaryFourOrderedFixedMeasured.envelope s K i cap+1100

theorem restore_bounds (store : BinarySeedLookupTree.Store) (ordered : Ordered) (drawn : Result store) (P D U F : ℕ)
    (hp : ordered.2 ≤ P ∧ usage ordered.1.2 ≤ U) (hd : drawn.2 ≤ D ∧ usage drawn.1.2 ≤ F) :
    (restore store ordered drawn).2 ≤ P+D+1700 ∧ usage (restore store ordered drawn).1.2 ≤ U+F+1100 := by
  let restored := BinaryThreeReferenceMeasured.references 4 (fun j => drawn.1.1.1.read (ordered.1.1.2 j))
  have hRestored : restored.2 ≤ 1616 ∧ usage restored.1.2 ≤ 915 :=
    ⟨BinaryThreeReferenceMeasured.references_work 4 _,BinaryThreeReferenceMeasured.references_usage 4 _⟩
  have hw := wrap_usage 40 3 [ordered.1.2,drawn.1.2,restored.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change ordered.2+drawn.2+restored.2+12 ≤ _ ∧ usage (wrap 40 3 [ordered.1.2,drawn.1.2,restored.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem afterOrder_bounds (store : BinarySeedLookupTree.Store) (input : Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (P U : ℕ) (hOrder : ordered.2 ≤ P ∧ usage ordered.1.2 ≤ U)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrder store input hC hAd ordered hOrdered K outer scalar pc hp).2 ≤ P+BinaryFourOrderedFixedMeasured.workEnvelope s K store.width store.cap.value+1700 ∧
      usage (afterOrder store input hC hAd ordered hOrdered K outer scalar pc hp).1.2 ≤ U+BinaryFourOrderedFixedMeasured.envelope s K store.width store.cap.value+1100 := by
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  have hRef : ordered.1.1.1.Refines source.input := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_refines input source hC hR
  let drawn := BinaryFourOrderedFixedMeasured.run store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  have hDraw := BinaryFourOrderedFixedMeasured.run_bounds store ordered.1.1.1 source.input hOrderedC hRef hOrderedAd s hs hH.input K outer scalar pc hp
  have hResult := restore_bounds store ordered drawn _ _ _ _ hOrder hDraw
  unfold afterOrder
  with_reducible exact hResult

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input hC hAd K outer scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  have hLength : ∀ j,RationalHeight (value (input.length.read j)) s := by intro j; rw [hR.2.1 j]; exact hH.2.1 j
  have hOrder : (BinaryFourOrderMeasured.ordered input).2 ≤ BinaryFourOrderMeasured.workEnvelope s ∧
      usage (BinaryFourOrderMeasured.ordered input).1.2 ≤ BinaryFourOrderLifetime.orderedEnvelope s :=
    ⟨BinaryFourOrderMeasured.ordered_work input hC s hLength,
      by rw [BinaryFourOrderMeasured.ordered_erases]; exact BinaryFourOrderLifetime.orderedWithTrace_usage input hC s hLength⟩
  have hResult := afterOrder_bounds store input source hC hR hAd s hs hH _
    ((congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans (BinaryFourOrderLifetime.orderedWithTrace_erasure input)) _ _ hOrder K outer scalar pc hp
  unfold run workEnvelope envelope
  with_reducible exact hResult

theorem run_position (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K outer scalar pc hp).1.1.2.value ∧ (run store input hC hAd K outer scalar pc hp).1.1.2.value ≤ store.cap.value := by
  unfold run
  rw [afterOrder_data]
  exact BinaryFourRestoredFixedLifetime.afterOrderWithTrace_position store input hC hAd _ _ _ K outer scalar pc hp

theorem run_cursor (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1.2 =
      (BinaryPRGWordControllerFour.restoredRun store input hC hAd K outer scalar pc hp).2 := by
  unfold run
  rw [afterOrder_data]
  exact BinaryFourRestoredFixedLifetime.afterOrderWithTrace_cursor store input hC hAd _ _ _ K outer scalar pc hp

theorem run_data (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1 =
      (BinaryFourRestoredFixedLifetime.runWithTrace store input hC hAd K outer scalar pc hp).1 := by
  apply Prod.ext
  · exact (run_window store input hC hAd K outer scalar pc hp).trans
      (BinaryFourRestoredFixedLifetime.runWithTrace_window store input hC hAd K outer scalar pc hp).symm
  · exact (run_cursor store input hC hAd K outer scalar pc hp).trans
      (BinaryFourRestoredFixedLifetime.runWithTrace_cursor store input hC hAd K outer scalar pc hp).symm

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K outer scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryFourRestoredFixedMeasured
