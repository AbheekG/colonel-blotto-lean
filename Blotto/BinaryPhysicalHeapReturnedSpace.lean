import Blotto.BinaryPhysicalHeapRequestLifetime

/-! The selected one-pass request's retained source trace, with the two-builder
term kept at the allowance from the returned heaps. These proof envelopes do
not add computations to the selected runner. Native reference-bit ownership
and host allocation remain separate from this source trace model. -/

namespace Blotto.BinaryPhysicalHeapReturnedSpace
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPhysicalHeapRequestLifetime
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {n : ℕ}

def buildCharge (request : Request n) (rich : Bool) : ℕ :=
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    request).1.1.getD ([],[])
  (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
    words.1 (if rich then words.1 else words.2)).2

def initialEnvelope (n W builder : ℕ) : ℕ :=
  let K := BinaryPRGHeapResourceInputBounds.initialHeapBound n W
  33 * (BinaryPRGWordStoreHeapMachine.countBound n 0 + builder) + 6*n+130+
    BinaryPRGHeapEnumerationLifetime.envelope n (binaryWordWidth n) +
    BinaryPRGHeapScanLifetime.scanEnvelope K K (binaryWordWidth n) W n + 54

theorem buildCharge_eq_arrays (request : Request n) (rich : Bool) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    buildCharge request rich =
      (BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork
        selected.length.data.toList selected.resource.data.toList).2 := by
  have hWords :
      (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
        request).1.1.getD ([],[]) =
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
    change (BinaryPhysicalNumericalReadbackLifetime.readPairWithTrace request).1.getD
      ([],[]) = _
    rw [BinaryPhysicalNumericalReadbackLifetime.request_pair_words]
    rfl
  unfold buildCharge
  rw [hWords]
  cases rich <;> rfl

theorem initial_trace_usage (request : Request n) (rich : Bool)
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width
      ((BinaryPRGResourceWork.resourceInput request.logical.request rich).length.read j) ≤ W)
    (hResource : ∀ j,width
      ((BinaryPRGResourceWork.resourceInput request.logical.request rich).resource.read j) ≤ W) :
    let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
    usage (BinaryPRGHeapInitialLifetime.initialWithTrace
      selected.length selected.resource
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2).2 ≤
      initialEnvelope n W (buildCharge request rich) := by
  have h := BinaryPhysicalHeapInitialLifetime.initialWithTrace_returned_build_usage
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request.logical.request rich).2.2
    W hW hCapacity hResource
  rw [← buildCharge_eq_arrays request rich] at h
  exact h

theorem initialEnvelope_le_input (request : Request n) (rich : Bool)
    (W : ℕ) (hW : 1 ≤ W)
    (hCapacity : ∀ j,width
      ((BinaryPRGResourceWork.resourceInput request.logical.request rich).length.read j) ≤ W)
    (hResource : ∀ j,width
      ((BinaryPRGResourceWork.resourceInput request.logical.request rich).resource.read j) ≤ W) :
    initialEnvelope n W (buildCharge request rich) ≤
      BinaryPRGHeapInitialLifetimeBound.envelope n W (binaryWordWidth n) := by
  have hBuild := BinaryPhysicalHeapInputLifetime.rawArraysWithTraceAndBuildWork_input_bound
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).length
    (BinaryPRGResourceWork.resourceInput request.logical.request rich).resource
    W hW hCapacity hResource
  rw [← buildCharge_eq_arrays request rich] at hBuild
  have hm := Nat.mul_le_mul_left 33 hBuild
  dsimp [initialEnvelope,BinaryPRGHeapInitialLifetimeBound.envelope,
    BinaryPRGHeapInitialLifetimeBound.buildEnvelope]
  nlinarith only [hm]

noncomputable def runEnvelope (request : Request n) (rich : Bool)
    (indexWidth seedCap : ℕ) : ℕ :=
  let D := request.logical.request.source.normalizedInput.latticeDenominator
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  initialEnvelope n W (buildCharge request rich) +
    BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope n W D indexWidth seedCap +
    BinaryPRGHeapMaterializationLifetime.envelope n
      (BinaryPRGHeapResourceInputCost.heapBound n W D) (binaryWordWidth n) +
    2*indexWidth+168

theorem accepted_nativeAt_usage_of_initial (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (I : ℕ)
    (hInitial : usage (BinaryPRGHeapInitialLifetime.initialWithTrace
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
      (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2 ≤ I) :
    let request := parsed.1.2.logical.request
    let D := request.source.normalizedInput.latticeDenominator
    let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
    usage (nativeAtWithTrace seed parsed.1.2 rich pc hp).2 ≤
      2000000200*(frame.length+3)^7+I+
        BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
          seed.width seed.cap.value+
        BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1
          (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
          (binaryWordWidth parsed.1.1)+120 := by
  let request := parsed.1.2.logical.request
  let selected := BinaryPRGResourceWork.resourceInput request rich
  let D := request.source.normalizedInput.latticeDenominator
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  let hC := (BinaryPRGResourceWork.resource_canonical request rich).2.1
  let hR := (BinaryPRGResourceWork.resource_canonical request rich).2.2
  obtain ⟨hl,hr,hb,hrb⟩ := BinaryPRGResourceWork.resource_lattice_boxes request rich
  obtain ⟨hcWidth,hrWidth⟩ := BinaryPRGHeapResourceRequest.input_widths request rich
  have hW : 1 ≤ W := by
    unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  have hCapacity : ∀ j,width (selected.length.read j) ≤ W := by
    intro j
    exact (hcWidth j).trans (by
      unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      omega)
  have hResource : ∀ j,width (selected.resource.read j) ≤ W := by
    intro j
    exact (hrWidth j).trans (by
      unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      omega)
  have hLoopOld := BinaryPRGHeapLifetimePolynomial.original_array_loop_usage
    seed selected.length selected.resource hC hR W D hW
    request.source.normalizedInput.latticeDenominator_pos
    hCapacity hResource hl hb hr hrb pc hp
  have hLoop : usage (BinaryPRGHeapLoopLifetime.runWithTrace seed
      (BinaryPRGHeapInitialLifetime.initialWithTrace selected.length selected.resource
        hC hR).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical selected.length hC)
      (BinaryPRGHeapInitialLifetime.initialWithTrace selected.length selected.resource
        hC hR).1.2 pc hp).2 ≤
      BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
        seed.width seed.cap.value := by
    rw [BinaryPRGHeapInitialLifetime.initialWithTrace_erasure]
    exact hLoopOld
  have hHeap : ∀ state : BinaryPRGHeapResourceLoop.Finished
      (capStore selected.length) parsed.1.1 (count selected.length),
      (sourceAtWithTrace seed parsed.1.2 rich pc hp).1.2.1 = some state →
        state.heap.tape.length ≤
          BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D := by
    intro state hSome
    apply BinaryPRGHeapNativeLifetimeBound.returned_heap seed
      selected.length selected.resource hC hR W D hW
      request.source.normalizedInput.latticeDenominator_pos
      hCapacity hResource hl hb hr hrb pc hp state
    rw [← sourceAt_erasure]
    exact hSome
  have hNative := nativeAt_usage frame parsed hParsed seed rich pc hp I
    (BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
      seed.width seed.cap.value)
    (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
    hInitial hLoop hHeap
  have hm := BinaryPRGHeapNativeLifetimeBound.materialization_depth_mono
    parsed.1.1 (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
    (BinaryPRGHeapResourceInputBounds.source_depth selected.length)
  change BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1
      (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
      (capStore (BinaryPRGResourceWork.resourceInput
        parsed.1.2.logical.request rich).length).width ≤
    BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1
      (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
      (binaryWordWidth parsed.1.1) at hm
  change usage (nativeAtWithTrace seed parsed.1.2 rich pc hp).2 ≤
    2000000200*(frame.length+3)^7+I+
      BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
        seed.width seed.cap.value+
      BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1
        (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
        (binaryWordWidth parsed.1.1)+120
  omega

theorem run_trace_usage_of_native (seed : BinarySeedLookupTree.Store)
    (request : Request n) (rich : Bool) (N : ℕ)
    (hNative : usage (nativeAtWithTrace seed request rich
      (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)).2 ≤ N) :
    usage (runWithTrace seed request rich).2 ≤ N+2*seed.width+48 := by
  let pc := BinaryWordIndexCoinController.zeroIndex seed
  have hp : pc.value ≤ seed.cap.value := by
    rw [BinaryWordIndexCoinController.zeroIndex_value]
    omega
  have hAt := wrap_usage 24 2 [(nativeAtWithTrace seed request rich pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hAt
  change usage (runAtWithTrace seed request rich pc hp).2 ≤
    24+2+(usage (nativeAtWithTrace seed request rich pc hp).2+2+0) at hAt
  change usage (nativeAtWithTrace seed request rich pc hp).2 ≤ N at hNative
  have hTop := wrapList_usage seed.cap.bits.length 16 (seed.cap.bits.length+2)
    [(runAtWithTrace seed request rich pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,seed.cap.size] at hTop
  unfold BinaryPhysicalHeapRequestLifetime.runWithTrace
  dsimp only
  simp only [seed.cap.size]
  change usage (wrapList seed.width 16 (seed.width+2)
    [(runAtWithTrace seed request rich pc hp).2]) ≤ N+2*seed.width+48
  omega

theorem accepted_selected_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) :
    usage (runWithTraceAndResidualAndBuildWork seed parsed.1.2 rich).1.2 ≤
      2000000200*(frame.length+3)^7+
        runEnvelope parsed.1.2 rich seed.width seed.cap.value := by
  let request := parsed.1.2.logical.request
  let D := request.source.normalizedInput.latticeDenominator
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  let I := initialEnvelope parsed.1.1 W (buildCharge parsed.1.2 rich)
  obtain ⟨hcWidth,hrWidth⟩ := BinaryPRGHeapResourceRequest.input_widths request rich
  have hW : 1 ≤ W := by
    unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  have hCapacity : ∀ j,width
      ((BinaryPRGResourceWork.resourceInput request rich).length.read j) ≤ W := by
    intro j
    exact (hcWidth j).trans (by
      unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      omega)
  have hResource : ∀ j,width
      ((BinaryPRGResourceWork.resourceInput request rich).resource.read j) ≤ W := by
    intro j
    exact (hrWidth j).trans (by
      unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      omega)
  have hInitial := initial_trace_usage parsed.1.2 rich W hW hCapacity hResource
  have hNative := accepted_nativeAt_usage_of_initial frame parsed hParsed seed rich
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega) I hInitial
  have hRun := run_trace_usage_of_native seed parsed.1.2 rich
    (2000000200*(frame.length+3)^7+I+
      BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
        seed.width seed.cap.value+
      BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1
        (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
        (binaryWordWidth parsed.1.1)+120) hNative
  rw [runWithTraceAndResidualAndBuildWork_erases]
  change usage (runWithTrace seed parsed.1.2 rich).2 ≤
    2000000200*(frame.length+3)^7+
      (I+BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope parsed.1.1 W D
        seed.width seed.cap.value+
      BinaryPRGHeapMaterializationLifetime.envelope parsed.1.1
        (BinaryPRGHeapResourceInputCost.heapBound parsed.1.1 W D)
        (binaryWordWidth parsed.1.1)+2*seed.width+168)
  omega

theorem runEnvelope_le_input (request : Request n) (rich : Bool)
    (indexWidth seedCap : ℕ) :
    runEnvelope request rich indexWidth seedCap ≤
      BinaryPRGHeapRequestLifetime.envelope request.logical.request indexWidth seedCap+
        2*indexWidth+40 := by
  let D := request.logical.request.source.normalizedInput.latticeDenominator
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  obtain ⟨hcWidth,hrWidth⟩ :=
    BinaryPRGHeapResourceRequest.input_widths request.logical.request rich
  have hW : 1 ≤ W := by
    unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  have hCapacity : ∀ j,width
      ((BinaryPRGResourceWork.resourceInput request.logical.request rich).length.read j) ≤ W := by
    intro j
    exact (hcWidth j).trans (by
      unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      omega)
  have hResource : ∀ j,width
      ((BinaryPRGResourceWork.resourceInput request.logical.request rich).resource.read j) ≤ W := by
    intro j
    exact (hrWidth j).trans (by
      unfold W D BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      omega)
  have hInitial := initialEnvelope_le_input request rich W hW hCapacity hResource
  change initialEnvelope n W (buildCharge request rich)+
    BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope n W D indexWidth seedCap+
    BinaryPRGHeapMaterializationLifetime.envelope n
      (BinaryPRGHeapResourceInputCost.heapBound n W D) (binaryWordWidth n)+
    2*indexWidth+168 ≤ _
  unfold BinaryPRGHeapRequestLifetime.envelope BinaryPRGHeapNativeLifetimeBound.envelope
  change _ ≤ (BinaryPRGHeapInitialLifetimeBound.envelope n W (binaryWordWidth n)+
    BinaryPRGHeapLifetimePolynomial.arrayLoopEnvelope n W D indexWidth seedCap+
    BinaryPRGHeapMaterializationLifetime.envelope n
      (BinaryPRGHeapResourceInputCost.heapBound n W D) (binaryWordWidth n)+100+28)+
    2*indexWidth+40
  omega

theorem accepted_selected_all_prefix (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ) :
    let trace := (runWithTraceAndResidualAndBuildWork seed parsed.1.2 rich).1.2
    let B := 2000000200*(frame.length+3)^7+
      runEnvelope parsed.1.2 rich seed.width seed.cap.value
    retainedHeap borrowed trace steps ≤ borrowed+B ∧
      framePeak (trace.take steps) ≤ B :=
  all_prefix _ _ (accepted_selected_usage frame parsed hParsed seed rich) borrowed steps

end Blotto.BinaryPhysicalHeapReturnedSpace
