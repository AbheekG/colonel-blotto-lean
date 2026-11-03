import Blotto.BinaryFourSmallUniformDrawMeasured
import Blotto.BinaryFourSmallCoinMeasured
import Blotto.BinaryReflectedDrawMeasured
import Blotto.BinaryFourSmallLifetime

/-! One actual measured root coin feeds its returned absolute cursor to only
the reached measured uniform or reflected draw. Root/resource/selection
exhaustion and preceding complete output bytes are preserved. -/
namespace Blotto.BinaryFourSmallMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev Root (store : BinarySeedLookupTree.Store) := ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ
abbrev Result (store : BinarySeedLookupTree.Store) := (BinaryPRGWordControllerFour.Result store × Trace) × ℕ

set_option cleanup.letToHave false in
def afterRootWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) : ((Result store) × ℕ) × ℕ :=
  match root.1.1.1 with
  | none => (((((none,root.1.1.2),wrap 24 2 [root.1.2]),root.2+4),0),0)
  | some true =>
      let all := BinaryFourSmallUniformDrawMeasured.runWithFactoryExtras store input hC hAd K scalar root.1.1.2 hNext
      let produced := all.1
      let drawn := produced.1
      ((((drawn.1.1,wrap 32 2 [root.1.2,drawn.1.2]),root.2+drawn.2+8),produced.2),all.2)
  | some false =>
      let all := BinaryReflectedDrawMeasured.runWithFactoryExtras store input hC hAd K outer scalar root.1.1.2 hNext
      let produced := all.1
      let drawn := produced.1
      ((((drawn.1.1,wrap 32 2 [root.1.2,drawn.1.2]),root.2+drawn.2+8),produced.2),all.2)

def afterRootWithDrawExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) : (Result store) × ℕ :=
  (afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1

theorem afterRootWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    (afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1 = afterRootWithDrawExtras store input hC hAd K outer scalar root hNext := rfl

theorem afterRootWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    afterRootWithDrawExtras store input hC hAd K outer scalar root hNext =
  match root.1.1.1 with
  | none => ((((none,root.1.1.2),wrap 24 2 [root.1.2]),root.2+4),0)
  | some true =>
      let produced := BinaryFourSmallUniformDrawMeasured.runWithDrawExtras store input hC hAd K scalar root.1.1.2 hNext
      let drawn := produced.1
      (((drawn.1.1,wrap 32 2 [root.1.2,drawn.1.2]),root.2+drawn.2+8),produced.2)
  | some false =>
      let produced := BinaryReflectedDrawMeasured.runWithDrawExtras store input hC hAd K outer scalar root.1.1.2 hNext
      let drawn := produced.1
      (((drawn.1.1,wrap 32 2 [root.1.2,drawn.1.2]),root.2+drawn.2+8),produced.2) := by
  simp only [afterRootWithDrawExtras,afterRootWithFactoryExtras,BinaryFourSmallUniformDrawMeasured.preparedWithExtras_compat,BinaryFourSmallUniformDrawMeasured.runWithFactoryExtras_compat,BinaryReflectedDrawMeasured.afterResourceWithFactoryExtras_compat,BinaryReflectedDrawMeasured.fromReachedWithFactoryExtras_compat,BinaryReflectedDrawMeasured.runWithFactoryExtras_compat]
  split <;> rfl

def afterRoot (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) : Result store :=
  (afterRootWithDrawExtras store input hC hAd K outer scalar root hNext).1

theorem afterRootWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    (afterRootWithDrawExtras store input hC hAd K outer scalar root hNext).1 = afterRoot store input hC hAd K outer scalar root hNext := rfl

theorem afterRoot_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    afterRoot store input hC hAd K outer scalar root hNext =
  match root.1.1.1 with
  | none => (((none,root.1.1.2),wrap 24 2 [root.1.2]),root.2+4)
  | some true =>
      let drawn := BinaryFourSmallUniformDrawMeasured.run store input hC hAd K scalar root.1.1.2 hNext
      ((drawn.1.1,wrap 32 2 [root.1.2,drawn.1.2]),root.2+drawn.2+8)
  | some false =>
      let drawn := BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar root.1.1.2 hNext
      ((drawn.1.1,wrap 32 2 [root.1.2,drawn.1.2]),root.2+drawn.2+8) := by
  simp only [afterRoot,afterRootWithDrawExtras_record]
  split <;> rfl

set_option cleanup.letToHave false in
def runWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((Result store) × ℕ) × ℕ) × ℕ :=
  let produced := BinaryFourSmallCoinMeasured.sampleWithExtras store input pc hp
  let root := produced.1
  let all := afterRootWithFactoryExtras store input hC hAd K outer scalar root
    (by simpa only [root,produced,BinaryFourSmallCoinMeasured.sampleWithExtras_compat] using (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2)
  ((all.1,produced.2),all.2)

def runWithControlExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((Result store) × ℕ) × ℕ :=
  (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1

theorem runWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1 = runWithControlExtras store input hC hAd K outer scalar pc hp := rfl

theorem runWithControlExtras_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithControlExtras store input hC hAd K outer scalar pc hp =
  let produced := BinaryFourSmallCoinMeasured.sampleWithExtras store input pc hp
  let root := produced.1
  let drawn := afterRootWithDrawExtras store input hC hAd K outer scalar root
    (by simpa only [root,produced,BinaryFourSmallCoinMeasured.sampleWithExtras_compat] using (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2)
  (drawn,produced.2) := by
  simp only [runWithControlExtras,runWithFactoryExtras,BinaryFourSmallUniformDrawMeasured.preparedWithExtras_compat,BinaryFourSmallUniformDrawMeasured.runWithFactoryExtras_compat,BinaryReflectedDrawMeasured.afterResourceWithFactoryExtras_compat,BinaryReflectedDrawMeasured.fromReachedWithFactoryExtras_compat,BinaryReflectedDrawMeasured.runWithFactoryExtras_compat,afterRootWithFactoryExtras_compat]

def runWithDrawExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (Result store) × ℕ :=
  (runWithControlExtras store input hC hAd K outer scalar pc hp).1

theorem runWithControlExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithControlExtras store input hC hAd K outer scalar pc hp).1 = runWithDrawExtras store input hC hAd K outer scalar pc hp := rfl

theorem runWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runWithDrawExtras store input hC hAd K outer scalar pc hp =
  let root := BinaryFourSmallCoinMeasured.sample store input pc hp
  afterRootWithDrawExtras store input hC hAd K outer scalar root (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2 := by
  simp only [runWithDrawExtras,runWithControlExtras_record]
  rfl

def run (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store :=
  (runWithDrawExtras store input hC hAd K outer scalar pc hp).1

theorem runWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithDrawExtras store input hC hAd K outer scalar pc hp).1 = run store input hC hAd K outer scalar pc hp := rfl

theorem run_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    run store input hC hAd K outer scalar pc hp =
  let root := BinaryFourSmallCoinMeasured.sample store input pc hp
  afterRoot store input hC hAd K outer scalar root (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2 := by
  simp only [run,runWithDrawExtras_record]
  rfl

theorem run_data (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1 = (BinaryFourSmallLifetime.runWithTrace store input hC hAd K outer scalar pc hp).1 := by
  simp only [run_record,afterRoot_record,BinaryFourSmallLifetime.runWithTrace,BinaryFourSmallCoinMeasured.sample_erases,
    BinaryFourSmallUniformDrawMeasured.run_data,BinaryReflectedDrawMeasured.run_previous]
  cases (BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp).1.1 with
  | none => rfl
  | some branch => cases branch <;> rfl

theorem run_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).1.1 = BinaryPRGWordControllerFour.smallRun store input hC hAd K outer scalar pc hp :=
  (run_data store input hC hAd K outer scalar pc hp).trans (BinaryFourSmallLifetime.runWithTrace_erasure store input hC hAd K outer scalar pc hp)

def workEnvelope (s K i cap : ℕ) : ℕ := BinaryFourSmallCoinMeasured.workEnvelope s i cap+
  BinaryFourSmallUniformDrawMeasured.workEnvelope s K i cap+BinaryReflectedDrawMeasured.workEnvelope s K i cap+8

def envelope (s K i cap : ℕ) : ℕ := BinaryFourSmallCoinLifetime.envelope s i cap+
  BinaryFourSmallUniformDrawMeasured.envelope s K i cap+BinaryReflectedDrawMeasured.envelope s K i cap+128

theorem root_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryFourSmallCoinMeasured.sample store input pc hp).2 ≤ BinaryFourSmallCoinMeasured.workEnvelope s store.width store.cap.value ∧
      usage (BinaryFourSmallCoinMeasured.sample store input pc hp).1.2 ≤ BinaryFourSmallCoinLifetime.envelope s store.width store.cap.value := by
  have hw := BinaryFourSmallCoinMeasured.sample_work store input source hC hR s hH pc hp
  have hu := BinaryFourSmallCoinLifetime.sampleWithTrace_usage store input source hC hR s hH pc hp
  rw [← BinaryFourSmallCoinMeasured.sample_erases] at hu
  refine ⟨hw.trans ?_,hu.trans ?_⟩
  · simp only [BinaryFourSmallCoinMeasured.workEnvelope,BinaryWordCoinMeasured.samplePrice]
    gcongr <;> exact Nat.sub_le _ _
  · simp only [BinaryFourSmallCoinLifetime.envelope,BinaryWordCoinLifetime.sampleBound,BinaryWordCoinLifetime.localBound]
    gcongr <;> exact Nat.sub_le _ _

theorem afterRoot_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value)
    (hRoot : root.2 ≤ BinaryFourSmallCoinMeasured.workEnvelope s store.width store.cap.value ∧
      usage root.1.2 ≤ BinaryFourSmallCoinLifetime.envelope s store.width store.cap.value) :
    (afterRoot store input hC hAd K outer scalar root hNext).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (afterRoot store input hC hAd K outer scalar root hNext).1.2 ≤ envelope s K store.width store.cap.value := by
  have hUniform := BinaryFourSmallUniformDrawMeasured.run_bounds store input source hC hR hCase hAd s hs hH K scalar root.1.1.2 hNext
  have hReflected := BinaryReflectedDrawMeasured.run_bounds store input source hC hR hCase hAd s (by omega) hH K outer scalar root.1.1.2 hNext
  simp only [afterRoot_record]
  split
  · have hw := wrap_usage 24 2 [root.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change root.2+4 ≤ _ ∧ usage (wrap 24 2 [root.1.2]) ≤ _
    unfold workEnvelope envelope; exact ⟨by omega,by omega⟩
  · have hw := wrap_usage 32 2 [root.1.2,(BinaryFourSmallUniformDrawMeasured.run store input hC hAd K scalar root.1.1.2 hNext).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change root.2+(BinaryFourSmallUniformDrawMeasured.run store input hC hAd K scalar root.1.1.2 hNext).2+8 ≤ _ ∧ usage (wrap 32 2 [root.1.2,_]) ≤ _
    unfold workEnvelope envelope; exact ⟨by omega,by omega⟩
  · have hw := wrap_usage 32 2 [root.1.2,(BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar root.1.1.2 hNext).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change root.2+(BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar root.1.1.2 hNext).2+8 ≤ _ ∧ usage (wrap 32 2 [root.1.2,_]) ≤ _
    unfold workEnvelope envelope; exact ⟨by omega,by omega⟩

theorem run_bounds (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store input hC hAd K outer scalar pc hp).2 ≤ workEnvelope s K store.width store.cap.value ∧
      usage (run store input hC hAd K outer scalar pc hp).1.2 ≤ envelope s K store.width store.cap.value := by
  have hResult := afterRoot_bounds store input source hC hR hCase hAd s hs hH K outer scalar _
    (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2 (root_bounds store input source hC hR s hH pc hp)
  simp only [run_record]
  with_reducible exact hResult

theorem run_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store input hC hAd K outer scalar pc hp).1.1.2.value ∧
      (run store input hC hAd K outer scalar pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_erasure]; exact BinaryPRGWordControllerFour.smallRun_position store input hC hAd K outer scalar pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store input hC hAd K outer scalar pc hp).1.2 steps ≤ borrowed+envelope s K store.width store.cap.value ∧
      framePeak ((run store input hC hAd K outer scalar pc hp).1.2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp).2 borrowed steps

end Blotto.BinaryFourSmallMeasured
