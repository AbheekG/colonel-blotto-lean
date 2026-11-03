import Blotto.BinaryReflectedWholeArithmeticEntryWork
import Blotto.BinaryReflectedTraceSparsity

/-! The actual primitive producer's old work, division/coin/write extras,
coin/final emission and write emission compose through the complete reflected
source/native/draw. These named source ledgers and arithmetic entry visits
retain other native/initialization metadata and physical-model boundaries. -/
namespace Blotto.BinaryReflectedPrimitiveExtraWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {capacity : Store} {n : ℕ} {hCount : n=capacity.cap.value}

def loopTotal (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let produced := BinaryHeapLoopPrimitiveMeasured.runTraceWithWrites seed limits canonical state pc hp
  produced.1.1.1.2+produced.1.1.2+produced.1.2+produced.2

theorem loopTotal_record (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let produced := BinaryHeapLoopPrimitiveMeasured.runTraceWithWrites seed limits canonical state pc hp
    loopTotal seed limits canonical state pc hp = (BinaryHeapLoopPrimitiveMeasured.run seed limits canonical state pc hp).2+
      produced.1.1.2+produced.1.2+produced.2 := rfl

theorem loopTotal_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    loopTotal seed limits canonical state pc hp ≤
      48*(BinaryHeapLoopPrimitiveMeasured.run seed limits canonical state pc hp).2+
        5*(BinaryHeapLoopPrimitiveMeasured.run seed limits canonical state pc hp).1.2.length+16*n+2 := by
  have ht := BinaryHeapLoopPrimitiveMeasured.runTraceMeasured_total_dimension seed limits canonical state pc hp
  have hw := BinaryHeapLoopPrimitiveMeasured.runTraceWithWrites_write_bound seed limits canonical state pc hp
  change (BinaryHeapLoopPrimitiveMeasured.runTraceWithWrites seed limits canonical state pc hp).1.1.1.2+
    (BinaryHeapLoopPrimitiveMeasured.runTraceWithWrites seed limits canonical state pc hp).1.1.2+
    (BinaryHeapLoopPrimitiveMeasured.runTraceWithWrites seed limits canonical state pc hp).1.2 ≤
      16*(BinaryHeapLoopPrimitiveMeasured.run seed limits canonical state pc hp).2+
        5*(BinaryHeapLoopPrimitiveMeasured.run seed limits canonical state pc hp).1.2.length+16*n+2 at ht
  simp only [loopTotal]
  omega

def sourceExtra (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let initialized := BinaryReflectedInitialFused.initial capacity resource hC hR
  let produced := BinaryHeapLoopPrimitiveMeasured.runTraceWithWrites seed initialized.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) initialized.1.1.2 pc hp
  produced.1.1.2+produced.1.2+produced.2

def sourceTotal (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let initialized := BinaryReflectedInitialFused.initial capacity resource hC hR
  initialized.2+loopTotal seed initialized.1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) initialized.1.1.2 pc hp+3

theorem sourceTotal_record (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    sourceTotal seed capacity resource hC hR pc hp =
      (BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).2+sourceExtra seed capacity resource hC hR pc hp := by
  simp only [sourceTotal,BinaryReflectedNativeFused.source,sourceExtra,loopTotal_record]
  omega

theorem sourceTotal_bound (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    sourceTotal seed capacity resource hC hR pc hp ≤
      48*(BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).2+
        5*(BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).1.2.length+16*n+2 := by
  have hl := loopTotal_bound seed (BinaryReflectedInitialFused.initial capacity resource hC hR).1.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    (BinaryReflectedInitialFused.initial capacity resource hC hR).1.1.2 pc hp
  simp only [sourceTotal,BinaryReflectedNativeFused.source,BinaryResourceTraceLength.wrap_length,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

def nativeTotal (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let drawn := BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp
  let total := sourceTotal seed capacity resource hC hR pc hp
  match drawn.1.1.2.1 with
  | none => total+2
  | some state => total+(BinaryHeapMaterializationMeasured.materialize capacity
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
      drawn.1.1.1 (BinaryReflectedNativeFused.source_cap seed capacity resource hC hR pc hp) state).2+4

theorem nativeTotal_record (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    nativeTotal seed capacity resource hC hR pc hp =
      (BinaryReflectedNativeFused.native seed capacity resource hC hR pc hp).2+sourceExtra seed capacity resource hC hR pc hp := by
  simp only [nativeTotal,BinaryReflectedNativeFused.native,sourceTotal_record]
  cases h : (BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).1.1.2.1 <;> dsimp only <;> omega

theorem nativeTotal_bound (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    nativeTotal seed capacity resource hC hR pc hp ≤
      48*(BinaryReflectedNativeFused.native seed capacity resource hC hR pc hp).2+
        5*(BinaryReflectedNativeFused.native seed capacity resource hC hR pc hp).1.2.length+16*n+2 := by
  have hs := sourceTotal_bound seed capacity resource hC hR pc hp
  simp only [nativeTotal,BinaryReflectedNativeFused.native]
  cases h : (BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).1.1.2.1 <;>
    simp only [BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] <;> omega

def resourceDrawTotal (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  nativeTotal seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp+4

theorem resourceDrawTotal_record (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    resourceDrawTotal seed prepared pc hp = (BinaryReflectedResourceMeasured.draw seed prepared pc hp).2+
      sourceExtra seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp := by
  simp only [resourceDrawTotal,BinaryReflectedResourceMeasured.draw,nativeTotal_record]
  omega

theorem resourceDrawTotal_bound (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    resourceDrawTotal seed prepared pc hp ≤ 48*(BinaryReflectedResourceMeasured.draw seed prepared pc hp).2+
      5*(BinaryReflectedResourceMeasured.draw seed prepared pc hp).1.2.length+50 := by
  have hn := nativeTotal_bound seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp
  simp only [resourceDrawTotal,BinaryReflectedResourceMeasured.draw,BinaryResourceTraceLength.wrap_length,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

def resourceTotal (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let prepared := BinaryReflectedPreparationMeasured.prepare input hC
  prepared.2+resourceDrawTotal seed prepared.1.1 pc hp+8

theorem resourceTotal_record (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let prepared := (BinaryReflectedPreparationMeasured.prepare input hC).1.1
    resourceTotal seed input hC pc hp = (BinaryReflectedResourceMeasured.run seed input hC pc hp).2+
      sourceExtra seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp := by
  simp only [resourceTotal,BinaryReflectedResourceMeasured.run_record,BinaryReflectedResourceMeasured.join,resourceDrawTotal_record]
  omega

theorem resourceTotal_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    resourceTotal seed input hC pc hp ≤ 48*(BinaryReflectedResourceMeasured.run seed input hC pc hp).2+
      5*(BinaryReflectedResourceMeasured.run seed input hC pc hp).1.2.length+50 := by
  have hd := resourceDrawTotal_bound seed (BinaryReflectedPreparationMeasured.prepare input hC).1.1 pc hp
  simp only [resourceTotal,BinaryReflectedResourceMeasured.run_record,BinaryReflectedResourceMeasured.join,
    BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

def drawTotal (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let reached := BinaryReflectedResourceMeasured.run seed input hC pc hp
  let suffix := BinaryReflectedDrawMeasured.afterResource seed input hC hAd reached.1.1.1 pc hp reached.1.1.2
    (BinaryReflectedResourceMeasured.run_resource seed input hC pc hp) K outer scalar
  resourceTotal seed input hC pc hp+suffix.2+8

theorem drawTotal_record (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let prepared := (BinaryReflectedPreparationMeasured.prepare input hC).1.1
    drawTotal seed input hC hAd K outer scalar pc hp = (BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).2+
      sourceExtra seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp := by
  simp only [drawTotal,BinaryReflectedDrawMeasured.run_record,BinaryReflectedDrawMeasured.fromReached_record,
    BinaryReflectedDrawMeasured.join,resourceTotal_record]
  omega

theorem drawTotal_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    drawTotal seed input hC hAd K outer scalar pc hp ≤ 48*(BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).2+
      5*(BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).1.2.length+50 := by
  have hr := resourceTotal_bound seed input hC pc hp
  simp only [drawTotal,BinaryReflectedDrawMeasured.run_record,BinaryReflectedDrawMeasured.fromReached_record,BinaryReflectedDrawMeasured.join,
    BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

def joint (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ := drawTotal seed input hC hAd K outer scalar pc hp+
  BinaryReflectedWholeArithmeticEntryWork.draw seed input hC hAd K outer scalar pc hp

theorem joint_input_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (source : RationalFourInput) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    joint seed input hC hAd K outer scalar pc hp ≤
      48*BinaryReflectedDrawMeasured.workEnvelope s K seed.width seed.cap.value+
        17*BinaryReflectedDrawMeasured.envelope s K seed.width seed.cap.value+65 := by
  have hw := drawTotal_bound seed input hC hAd K outer scalar pc hp
  have he := BinaryReflectedWholeArithmeticEntryWork.draw_input_bound seed input source hC hR hCase hAd s hs hH K outer scalar pc hp
  have hpast := BinaryReflectedDrawMeasured.run_bounds seed input source hC hR hCase hAd s hs hH K outer scalar pc hp
  have ht := BinaryMeasuredTraceSparsity.length_usage _ (BinaryReflectedTraceSparsity.reflected_bound seed input hC hAd K outer scalar pc hp)
  simp only [joint]
  omega

end Blotto.BinaryReflectedPrimitiveExtraWork
