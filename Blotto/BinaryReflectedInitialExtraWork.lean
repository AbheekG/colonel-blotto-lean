import Blotto.BinaryHeapConstructionChargeOrder
import Blotto.BinaryReflectedPrimitiveExtraWork

/-! The selected reflected initializer actually reaches one measured counter,
two heap builders and their three emissions plus the enclosing emitted wrapper.
Their returned work/allocated-bit fields now join the complete reflected draw.
These are named source charges, not a native allocator or physical-space model. -/
namespace Blotto.BinaryReflectedInitialExtraWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {n : ℕ}

def arraysExtra (capacity resource : FixedArrayTable n SignedWord) : ℕ :=
  let counted := BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []
  let limits := BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 capacity.data.toList
  let bids := BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 resource.data.toList
  let emitted := BinaryInitialWrapperEmission.listThree (3*capacity.data.toList.length) 64 (3*capacity.data.toList.length+4)
    counted.1.1.2 limits.1.1.2 bids.1.1.2
  counted.1.2.work+counted.2+limits.2+bids.2+emitted.2

def arraysAllocated (capacity resource : FixedArrayTable n SignedWord) : ℕ :=
  let counted := BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []
  let limits := BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 capacity.data.toList
  let bids := BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 resource.data.toList
  counted.1.2.allocatedBits+limits.1.2.allocatedBits+bids.1.2.allocatedBits

theorem arraysExtra_bound (capacity resource : FixedArrayTable n SignedWord) :
    arraysExtra capacity resource ≤ 12*(n+1)^2+30*(BinaryReflectedInitialFused.arrays capacity resource).1.2.length+41 := by
  have hc := BinaryHeapConstructionPlan.count_emission_bound capacity.data.toList ([] : List Bool)
  have hl := BinaryHeapConstructionPlan.prepare_emission_bound BinaryRationalOpcode.zero
    (BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []).1.1.1 capacity.data.toList
  have hr := BinaryHeapConstructionPlan.prepare_emission_bound BinaryRationalOpcode.zero
    (BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []).1.1.1 resource.data.toList
  have hw : (BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []).1.2.work ≤
      BinaryPRGWordStoreHeapMachine.countBound capacity.data.toList.length ([] : List Bool).length := by
    rw [BinaryHeapConstructionPlan.count_compat]
    exact (BinaryPRGWordStoreHeapMachine.countWithWork_bounds capacity.data.toList ([] : List Bool)).1
  simp only [BinaryPRGWordStoreHeapMachine.countBound,Array.length_toList,capacity.size,List.length_nil,Nat.zero_add] at hw
  simp only [arraysExtra,BinaryReflectedInitialFused.arrays,BinaryInitialWrapperEmission.listThree_work,
    BinaryInitialWrapperEmission.listThree_length]
  nlinarith only [hc,hl,hr,hw]

theorem arraysAllocated_bound (capacity resource : FixedArrayTable n SignedWord) :
    arraysAllocated capacity resource ≤ (BinaryReflectedInitialFused.arrays capacity resource).2+12*(n+1)^2 := by
  have hc := BinaryHeapConstructionChargeOrder.counted capacity.data.toList ([] : List Bool)
  have hl := BinaryHeapConstructionChargeOrder.prepared BinaryRationalOpcode.zero
    (BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []).1.1.1 capacity.data.toList
  have hr := BinaryHeapConstructionChargeOrder.prepared BinaryRationalOpcode.zero
    (BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []).1.1.1 resource.data.toList
  have hw : (BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []).1.2.work ≤
      BinaryPRGWordStoreHeapMachine.countBound capacity.data.toList.length ([] : List Bool).length := by
    rw [BinaryHeapConstructionPlan.count_compat]
    exact (BinaryPRGWordStoreHeapMachine.countWithWork_bounds capacity.data.toList ([] : List Bool)).1
  simp only [BinaryPRGWordStoreHeapMachine.countBound,Array.length_toList,capacity.size,List.length_nil,Nat.zero_add] at hw
  simp only [arraysAllocated,BinaryReflectedInitialFused.arrays]
  nlinarith only [hc,hl,hr,hw,Nat.zero_le (2*capacity.data.toList.length-
    BinaryCarryCounter.ones (BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []).1.1.1)]

/-- The old amortized counter allowance is retained as a conservative extra;
all reached child work and all four emission records are covered. -/
theorem arrays_children (capacity resource : FixedArrayTable n SignedWord) :
    let counted := BinaryHeapConstructionPlan.countWithEmission capacity.data.toList []
    let limits := BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 capacity.data.toList
    let bids := BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 resource.data.toList
    counted.1.2.work+limits.1.2.work+bids.1.2.work+counted.2+limits.2+bids.2+
      (BinaryInitialWrapperEmission.listThree (3*capacity.data.toList.length) 64 (3*capacity.data.toList.length+4)
        counted.1.1.2 limits.1.1.2 bids.1.1.2).2 ≤
      (BinaryReflectedInitialFused.arrays capacity resource).2+arraysExtra capacity resource := by
  simp only [BinaryReflectedInitialFused.arrays,arraysExtra]
  omega

theorem initial_extra_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    arraysExtra capacity resource ≤ 12*(n+1)^2+
      30*(BinaryReflectedInitialFused.initial capacity resource hC hR).1.2.length+41 := by
  have h := arraysExtra_bound capacity resource
  simp only [BinaryReflectedInitialFused.initial,BinaryReflectedInitialFused.fromArrays,
    BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem initial_allocated_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    arraysAllocated capacity resource ≤ (BinaryReflectedInitialFused.initial capacity resource hC hR).2+12*(n+1)^2 := by
  have h := arraysAllocated_bound capacity resource
  simp only [BinaryReflectedInitialFused.initial]
  omega

theorem source_bounds (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    arraysExtra capacity resource ≤ 12*(n+1)^2+
      30*(BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).1.2.length+41 ∧
    arraysAllocated capacity resource ≤ (BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).2+12*(n+1)^2 := by
  have he := initial_extra_bound capacity resource hC hR
  have ha := initial_allocated_bound capacity resource hC hR
  simp only [BinaryReflectedNativeFused.source,BinaryResourceTraceLength.wrap_length,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  exact ⟨by omega,by omega⟩

theorem native_bounds (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    arraysExtra capacity resource ≤ 12*(n+1)^2+
      30*(BinaryReflectedNativeFused.native seed capacity resource hC hR pc hp).1.2.length+41 ∧
    arraysAllocated capacity resource ≤ (BinaryReflectedNativeFused.native seed capacity resource hC hR pc hp).2+12*(n+1)^2 := by
  have h := source_bounds seed capacity resource hC hR pc hp
  simp only [BinaryReflectedNativeFused.native]
  cases hState : (BinaryReflectedNativeFused.source seed capacity resource hC hR pc hp).1.1.2.1 <;>
    simp only [BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] <;>
    exact ⟨by omega,by omega⟩

theorem resource_draw_bounds (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    arraysExtra prepared.capacity prepared.system.initial ≤ 30*(BinaryReflectedResourceMeasured.draw seed prepared pc hp).1.2.length+233 ∧
    arraysAllocated prepared.capacity prepared.system.initial ≤ (BinaryReflectedResourceMeasured.draw seed prepared pc hp).2+192 := by
  have h := native_bounds seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp
  simp only [BinaryReflectedResourceMeasured.draw,BinaryResourceTraceLength.wrap_length,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  exact ⟨by omega,by omega⟩

theorem resource_bounds (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let prepared := (BinaryReflectedPreparationMeasured.prepare input hC).1.1
    arraysExtra prepared.capacity prepared.system.initial ≤ 30*(BinaryReflectedResourceMeasured.run seed input hC pc hp).1.2.length+233 ∧
    arraysAllocated prepared.capacity prepared.system.initial ≤ (BinaryReflectedResourceMeasured.run seed input hC pc hp).2+192 := by
  have h := resource_draw_bounds seed (BinaryReflectedPreparationMeasured.prepare input hC).1.1 pc hp
  simp only [BinaryReflectedResourceMeasured.run_record,BinaryReflectedResourceMeasured.join,
    BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  exact ⟨by omega,by omega⟩

def drawInitialExtra (input : BinaryFourParameters.Input) (hC : input.Canonical) : ℕ :=
  let prepared := (BinaryReflectedPreparationMeasured.prepare input hC).1.1
  arraysExtra prepared.capacity prepared.system.initial

def drawAllocated (input : BinaryFourParameters.Input) (hC : input.Canonical) : ℕ :=
  let prepared := (BinaryReflectedPreparationMeasured.prepare input hC).1.1
  arraysAllocated prepared.capacity prepared.system.initial

theorem draw_initial_bounds (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    drawInitialExtra input hC ≤ 30*(BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).1.2.length+233 ∧
    drawAllocated input hC ≤ (BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).2+192 := by
  have h := resource_bounds seed input hC pc hp
  simp only [drawInitialExtra,drawAllocated,BinaryReflectedDrawMeasured.run_record,BinaryReflectedDrawMeasured.fromReached_record,
    BinaryReflectedDrawMeasured.join,BinaryResourceTraceLength.wrap_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  exact ⟨by omega,by omega⟩

def drawTotal (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  BinaryReflectedPrimitiveExtraWork.drawTotal seed input hC hAd K outer scalar pc hp+drawInitialExtra input hC

theorem drawTotal_record (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let prepared := (BinaryReflectedPreparationMeasured.prepare input hC).1.1
    drawTotal seed input hC hAd K outer scalar pc hp = (BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).2+
      BinaryReflectedPrimitiveExtraWork.sourceExtra seed prepared.capacity prepared.system.initial
        prepared.capacity_canonical prepared.canonical.2.2.2 pc hp+arraysExtra prepared.capacity prepared.system.initial := by
  simp only [drawTotal,BinaryReflectedPrimitiveExtraWork.drawTotal_record,drawInitialExtra]

theorem drawTotal_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    drawTotal seed input hC hAd K outer scalar pc hp ≤ 48*(BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).2+
      35*(BinaryReflectedDrawMeasured.run seed input hC hAd K outer scalar pc hp).1.2.length+283 := by
  have hpast := BinaryReflectedPrimitiveExtraWork.drawTotal_bound seed input hC hAd K outer scalar pc hp
  have hi := (draw_initial_bounds seed input hC hAd K outer scalar pc hp).1
  simp only [drawTotal]
  omega

def joint (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  drawTotal seed input hC hAd K outer scalar pc hp+
    BinaryReflectedWholeArithmeticEntryWork.draw seed input hC hAd K outer scalar pc hp+drawAllocated input hC

theorem joint_input_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (source : RationalFourInput) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    joint seed input hC hAd K outer scalar pc hp ≤
      49*BinaryReflectedDrawMeasured.workEnvelope s K seed.width seed.cap.value+
        107*BinaryReflectedDrawMeasured.envelope s K seed.width seed.cap.value+580 := by
  have hw := drawTotal_bound seed input hC hAd K outer scalar pc hp
  have ha := (draw_initial_bounds seed input hC hAd K outer scalar pc hp).2
  have he := BinaryReflectedWholeArithmeticEntryWork.draw_input_bound seed input source hC hR hCase hAd s hs hH K outer scalar pc hp
  have hpast := BinaryReflectedDrawMeasured.run_bounds seed input source hC hR hCase hAd s hs hH K outer scalar pc hp
  have ht := BinaryMeasuredTraceSparsity.length_usage _ (BinaryReflectedTraceSparsity.reflected_bound seed input hC hAd K outer scalar pc hp)
  simp only [joint]
  omega

theorem joint_input_width (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (source : RationalFourInput) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    binaryWordWidth (joint seed input hC hAd K outer scalar pc hp) ≤
      binaryWordWidth (49*BinaryReflectedDrawMeasured.workEnvelope s K seed.width seed.cap.value+
        107*BinaryReflectedDrawMeasured.envelope s K seed.width seed.cap.value+580) :=
  binaryWordWidth_mono (joint_input_bound seed input hC hAd K outer scalar pc hp source hR hCase s hs hH)

end Blotto.BinaryReflectedInitialExtraWork
