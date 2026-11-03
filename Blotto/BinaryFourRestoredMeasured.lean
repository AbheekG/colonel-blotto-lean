import Blotto.BinaryFourOrderedMeasured
import Blotto.BinaryFourOrderMeasured
import Blotto.BinaryFourRestoredLifetime

/-! Actual measured sorting feeds the complete measured ordered draw. Only a
successful four-word row is restored by measured reference packing; the
optional output and absolute cursor retain the preceding controller semantics. -/
namespace Blotto.BinaryFourRestoredMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev Input := BinaryFourSpecSampler.Input
abbrev Ordered := ((BinaryFourParameters.Input × Equiv.Perm (Fin 4)) × Trace) × ℕ
abbrev Result (store : BinarySeedLookupTree.Store) := (BinaryPRGWordControllerFour.Result store × Trace) × ℕ

def restore (store : BinarySeedLookupTree.Store) (ordered : Ordered) (drawn : Result store) : Result store :=
  match drawn.1.1.1 with
  | none => (((none,drawn.1.1.2),wrap 32 2 [ordered.1.2,drawn.1.2]),ordered.2+drawn.2+8)
  | some row =>
      let restored := BinaryThreeReferenceMeasured.references 4 (fun j => row.read (ordered.1.1.2 j))
      (((some restored.1.1,drawn.1.1.2),wrap 40 3 [ordered.1.2,drawn.1.2,restored.1.2]),ordered.2+drawn.2+restored.2+12)

set_option cleanup.letToHave false in
def afterOrderWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((Result store) × ℕ) × ℕ) × ℕ :=
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  let all := BinaryFourOrderedMeasured.runWithFactoryExtras store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  let produced := all.1.1
  (((restore store ordered produced.1,produced.2),all.1.2),all.2)

def afterOrderWithControlExtras (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((Result store) × ℕ) × ℕ :=
  (afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1

theorem afterOrderWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1 = afterOrderWithControlExtras store input hC hAd ordered hOrdered K outer scalar pc hp := rfl

theorem afterOrderWithControlExtras_record (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    afterOrderWithControlExtras store input hC hAd ordered hOrdered K outer scalar pc hp =

  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  let all := BinaryFourOrderedMeasured.runWithControlExtras store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  let produced := all.1
  ((restore store ordered produced.1,produced.2),all.2) := by
  simp only [afterOrderWithControlExtras,afterOrderWithFactoryExtras,BinaryFourOrderedMeasured.runWithFactoryExtras_compat]

def afterOrderWithDrawExtras (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (Result store) × ℕ :=
  (afterOrderWithControlExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1

theorem afterOrderWithControlExtras_compat (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithControlExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1 = afterOrderWithDrawExtras store input hC hAd ordered hOrdered K outer scalar pc hp := rfl

theorem afterOrderWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    afterOrderWithDrawExtras store input hC hAd ordered hOrdered K outer scalar pc hp =
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  let produced := BinaryFourOrderedMeasured.runWithDrawExtras store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  (restore store ordered produced.1,produced.2) := by
  simp only [afterOrderWithDrawExtras,afterOrderWithControlExtras_record]
  rfl

def afterOrder (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  (afterOrderWithDrawExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1

theorem afterOrderWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithDrawExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1 = afterOrder store input hC hAd ordered hOrdered K outer scalar pc hp := rfl

theorem afterOrder_record (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    afterOrder store input hC hAd ordered hOrdered K outer scalar pc hp =
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  let drawn := BinaryFourOrderedMeasured.run store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  restore store ordered drawn := by
  simp only [afterOrder,afterOrderWithDrawExtras_record]
  rfl

set_option cleanup.letToHave false in
def runWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((Result store) × ℕ) × ℕ) × ℕ :=
  let ordered := BinaryFourOrderMeasured.ordered input
  afterOrderWithFactoryExtras store input hC hAd ordered ((congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input)) K outer scalar pc hp

def runWithControlExtras (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((Result store) × ℕ) × ℕ :=
  (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1

theorem runWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1 = runWithControlExtras store input hC hAd K outer scalar pc hp := rfl

theorem runWithControlExtras_record (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithControlExtras store input hC hAd K outer scalar pc hp =

  let ordered := BinaryFourOrderMeasured.ordered input
  afterOrderWithControlExtras store input hC hAd ordered ((congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input)) K outer scalar pc hp := by
  simp only [runWithControlExtras,runWithFactoryExtras,BinaryFourOrderedMeasured.runWithFactoryExtras_compat,afterOrderWithFactoryExtras_compat]

def runWithDrawExtras (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (Result store) × ℕ :=
  (runWithControlExtras store input hC hAd K outer scalar pc hp).1

theorem runWithControlExtras_compat (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithControlExtras store input hC hAd K outer scalar pc hp).1 = runWithDrawExtras store input hC hAd K outer scalar pc hp := rfl

theorem runWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithDrawExtras store input hC hAd K outer scalar pc hp =
  let ordered := BinaryFourOrderMeasured.ordered input
  afterOrderWithDrawExtras store input hC hAd ordered ((congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input)) K outer scalar pc hp := by
  simp only [runWithDrawExtras,runWithControlExtras_record]
  rfl

def run (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  (runWithDrawExtras store input hC hAd K outer scalar pc hp).1

theorem runWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithDrawExtras store input hC hAd K outer scalar pc hp).1 = run store input hC hAd K outer scalar pc hp := rfl

theorem run_record (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store input hC hAd K outer scalar pc hp =
  let ordered := BinaryFourOrderMeasured.ordered input
  afterOrder store input hC hAd ordered ((congrArg Prod.fst (BinaryFourOrderMeasured.ordered_erases input)).trans
    (BinaryFourOrderLifetime.orderedWithTrace_erasure input)) K outer scalar pc hp := by
  simp only [run,runWithDrawExtras_record]
  rfl

theorem afterOrder_data (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrder store input hC hAd ordered hOrdered K outer scalar pc hp).1.1 =
      (BinaryFourRestoredLifetime.afterOrderWithTrace store input hC hAd ordered.1.1 hOrdered ordered.1.2 K outer scalar pc hp).1 := by
  simp only [afterOrder_record,restore,BinaryFourRestoredLifetime.afterOrderWithTrace]
  rw [BinaryFourOrderedMeasured.run_data]
  cases (BinaryFourOrderedLifetime.runWithTrace store ordered.1.1.1
    (by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC)
    (by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd) K outer scalar pc hp).1.1 with
  | none => rfl
  | some row => simp only [BinaryThreeReferenceMeasured.references_data,BinaryNestedResidualLifetime.copyWithTrace_erasure]

theorem run_erasure (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1 = BinaryPRGWordControllerFour.restoredRun store input hC hAd K outer scalar pc hp := by
  simp only [run_record]
  exact (afterOrder_data store input hC hAd _ _ K outer scalar pc hp).trans
    (BinaryFourRestoredLifetime.afterOrderWithTrace_erasure store input hC hAd _ _ _ K outer scalar pc hp)

def workEnvelope (s K i cap : ℕ) : ℕ := BinaryFourOrderMeasured.workEnvelope s+BinaryFourOrderedMeasured.workEnvelope s K i cap+1700

def envelope (s K i cap : ℕ) : ℕ := BinaryFourOrderLifetime.orderedEnvelope s+BinaryFourOrderedMeasured.envelope s K i cap+1100

theorem restore_bounds (store : BinarySeedLookupTree.Store) (ordered : Ordered) (drawn : Result store) (P D U F : ℕ)
    (hp : ordered.2 ≤ P ∧ usage ordered.1.2 ≤ U) (hd : drawn.2 ≤ D ∧ usage drawn.1.2 ≤ F) :
    (restore store ordered drawn).2 ≤ P+D+1700 ∧ usage (restore store ordered drawn).1.2 ≤ U+F+1100 := by
  unfold restore
  split
  · have hw := wrap_usage 32 2 [ordered.1.2,drawn.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change ordered.2+drawn.2+8 ≤ _ ∧ usage (wrap 32 2 [ordered.1.2,drawn.1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · rename_i row hRow
    let restored := BinaryThreeReferenceMeasured.references 4 (fun j => row.read (ordered.1.1.2 j))
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
    (afterOrder store input hC hAd ordered hOrdered K outer scalar pc hp).2 ≤ P+BinaryFourOrderedMeasured.workEnvelope s K store.width store.cap.value+1700 ∧
      usage (afterOrder store input hC hAd ordered hOrdered K outer scalar pc hp).1.2 ≤ U+BinaryFourOrderedMeasured.envelope s K store.width store.cap.value+1100 := by
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  have hRef : ordered.1.1.1.Refines source.input := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_refines input source hC hR
  let drawn := BinaryFourOrderedMeasured.run store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  have hDraw := BinaryFourOrderedMeasured.run_bounds store ordered.1.1.1 source.input hOrderedC hRef hOrderedAd s hs hH.input K outer scalar pc hp
  have hResult := restore_bounds store ordered drawn _ _ _ _ hOrder hDraw
  simp only [afterOrder_record]
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
  simp only [run_record,workEnvelope,envelope]
  with_reducible exact hResult

theorem run_position (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K outer scalar pc hp).1.1.2.value ∧ (run store input hC hAd K outer scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_erasure]; exact BinaryPRGWordControllerFour.restoredRun_position store input hC hAd K outer scalar pc hp

theorem run_decoded (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerFour.decoded store (run store input hC hAd K outer scalar pc hp).1.1 =
      BinaryFourSpecPartialRun.runIndexed input hC hAd K store.cap.value outer scalar (BinaryWordIndexCoinController.reader store) pc.value hp := by
  rw [run_erasure]; exact BinaryPRGWordControllerFour.restoredRun_state store input hC hAd K outer scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K outer scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryFourRestoredMeasured
