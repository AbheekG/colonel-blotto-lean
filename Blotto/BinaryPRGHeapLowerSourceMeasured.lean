import Blotto.BinaryPRGHeapLowerMeasuredWork
import Blotto.BinaryPRGHeapLowerSourceBound

/-! Deterministic physical initialization, lower completion and native
materialization carry their existing source-component work with the actual
returned state and exact lifetime trace. Original three-array heights derive
every reached heap and width bound; no seed or reached-state oracle is an
execution argument. Full native-machine and observer costs remain separate. -/
namespace Blotto.BinaryPRGHeapLowerSourceMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGHeapResourceSource (capStore count)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceThreeSource (inputWidth initialCells pointerWidth heapCap)
open BinaryPRGHeapResourceThreeReservation (Reserved)
set_option maxHeartbeats 2000000
variable {n : ℕ}

def source (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    ((FixedBinaryWord (capStore capacity).width × Finished (capStore capacity) n (count capacity)) × Trace) × ℕ :=
  let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨prepared.1.1.ruler,prepared.1.1.size⟩
  let completed := BinaryPRGHeapLowerMeasuredWork.run prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2
  (((capWord,completed.1.1),wrap 32 2 [prepared.2,completed.1.2]),
    (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 + completed.2 + 3)

theorem source_erases (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (source capacity resource hC hR).1 =
      BinaryPRGHeapLowerSourceLifetime.sourceWithTrace capacity resource hC hR := by
  simp only [source,BinaryPRGHeapLowerSourceLifetime.sourceWithTrace,
    BinaryPRGHeapLowerMeasuredWork.run_erases]

theorem source_cap (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (source capacity resource hC hR).1.1.1 = (capStore capacity).cap := by
  rw [source_erases]
  exact BinaryPRGHeapLowerSourceLifetime.sourceWithTrace_cap capacity resource hC hR

def native (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (BinaryResourcePair.Certified capacity × Trace) × ℕ :=
  let drawn := source capacity resource hC hR
  let terminal := BinaryPRGHeapMaterializationLifetime.materializeWithTrace capacity
    (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    drawn.1.1.1 (source_cap capacity resource hC hR) drawn.1.1.2
  let terminalCharge := (BinaryPRGHeapResourceMaterialization.materializeWithWork capacity
    (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    drawn.1.1.1 (source_cap capacity resource hC hR) drawn.1.1.2).2
  ((terminal.1,wrap 24 2 [drawn.1.2,terminal.2]),drawn.2 + terminalCharge + 4)

theorem native_erases (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (native capacity resource hC hR).1 =
      BinaryPRGHeapLowerSourceLifetime.nativeWithTrace capacity resource hC hR := by
  simp only [native,BinaryPRGHeapLowerSourceLifetime.nativeWithTrace,source_erases]

theorem native_data (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (native capacity resource hC hR).1.1 =
      BinaryGeneralResourceFallback.choose hC (BinaryResourcePair.initial capacity resource hC hR) := by
  rw [native_erases]
  exact BinaryPRGHeapLowerSourceLifetime.nativeWithTrace_erasure capacity resource hC hR

theorem loop_work (s : ℕ) (hs : 2 ≤ s) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
    (BinaryPRGHeapLowerMeasuredWork.run prepared.1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) prepared.1.2).2 ≤
        BinaryPRGHeapResourceThreeSource.loopBound s 0 0 := by
  let prepared := BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR
  let cap := capStore capacity
  let W := inputWidth s
  let K := initialCells s
  let P := pointerWidth s
  let H := heapCap s
  have hInitial := BinaryPRGHeapLowerSourceBound.initial_bounds s capacity resource hC hR hCapacity hResource
  change prepared.1.1.heap.tape.length ≤ K ∧ prepared.1.2.heap.tape.length ≤ K ∧
    BinaryPRGHeapResourceThreeStep.HeightInv 2 s prepared.1.2 at hInitial
  have hd := BinaryPRGHeapResourceInputBounds.source_depth capacity
  change cap.width ≤ binaryWordWidth 3 at hd
  have hCap : ∀ j,RationalHeight (value ((BinaryPRGWordControllerBooleanResourceUpdate.table
      cap.cap cap.tree 3 (count capacity)).read j)) s := by
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hCapacity
  have hGrowth : BinaryPRGHeapResourceUpdateBudget.growth cap.width W P ≤
      BinaryPRGHeapResourceUpdateBudget.growth (binaryWordWidth 3) W P := by
    unfold BinaryPRGHeapResourceUpdateBudget.growth
    gcongr
  have hReserved : Reserved 2 s P H prepared.1.2 := by
    refine ⟨hInitial.2.2,?_⟩
    have hm := Nat.mul_le_mul prepared.1.2.active_length_le hGrowth
    exact (Nat.add_le_add hInitial.2.1 hm).trans
      (BinaryPRGHeapResourceReservation.source_room K 3 (binaryWordWidth 3) W)
  have hP : 0 < P := by unfold P pointerWidth BinaryPRGHeapResourceReservation.sourcePointerWidth; omega
  have hRoom : H < 2^P := BinaryPRGWordStoreHeap.quadratic_lt_capacity _
  let seed := BinarySeedLookupTree.prepare []
  have hBudget := BinaryPRGHeapResourceThreeReservation.reachableStepBudget
    (hC := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    2 s hs hCap seed prepared.1.1 K H P hInitial.1 hP hRoom
  have hLoop := BinaryPRGHeapLowerMeasuredWork.run_inputCount_work seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    (Reserved 2 s P H) _ hBudget prepared.1.2 hReserved
  exact hLoop.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3
    (Nat.mul_le_mul_left 2 (BinaryPRGHeapResourceThreeSource.stepBound_depth_mono hd))) 2)

def workEnvelope (s : ℕ) : ℕ :=
  BinaryPRGHeapResourceInputBounds.preparationBound 3 (inputWidth s) +
    BinaryPRGHeapResourceThreeSource.loopBound s 0 0 +
    BinaryPRGHeapResourceSourceReservation.terminalBound 3 (binaryWordWidth 3) (heapCap s) + 7

theorem native_work (s : ℕ) (hs : 2 ≤ s) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    (native capacity resource hC hR).2 ≤ workEnvelope s := by
  obtain ⟨hc,hr⟩ := BinaryPRGHeapThreeNativeLifetimeBound.input_widths s capacity resource hC hR hCapacity hResource
  have hW : 1 ≤ inputWidth s := by unfold inputWidth BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega
  have hI := BinaryPRGHeapResourceInputBounds.initialWithWork_input_bound
    capacity resource hC hR (inputWidth s) hW hc hr
  have hL := loop_work s hs capacity resource hC hR hCapacity hResource
  let drawn := source capacity resource hC hR
  have hHeap : drawn.1.1.2.heap.tape.length ≤ heapCap s := by
    dsimp only [drawn]
    rw [source_erases]
    exact BinaryPRGHeapLowerSourceBound.returned_heap s hs capacity resource hC hR hCapacity hResource
  have hT := (BinaryPRGHeapResourceMaterialization.materializeWithWork_uniformBound capacity
    (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    drawn.1.1.1 (source_cap capacity resource hC hR) drawn.1.1.2).trans
      (BinaryPRGHeapResourceSourceReservation.terminalUniformBound_le _
        (source_cap capacity resource hC hR) _ (heapCap s) hHeap)
  have hMono := BinaryPRGHeapResourceInputCost.terminalBound_mono (count := 3)
    (BinaryPRGHeapResourceInputBounds.source_depth capacity) (le_refl (heapCap s))
  have hS : drawn.2 ≤ BinaryPRGHeapResourceInputBounds.preparationBound 3 (inputWidth s) +
      BinaryPRGHeapResourceThreeSource.loopBound s 0 0 + 3 := by
    change _ + _ + 3 ≤ _
    omega
  have hResult : drawn.2 + (BinaryPRGHeapResourceMaterialization.materializeWithWork capacity
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
      drawn.1.1.1 (source_cap capacity resource hC hR) drawn.1.1.2).2 + 4 ≤ workEnvelope s := by
    unfold workEnvelope
    omega
  unfold native
  with_reducible exact hResult

theorem native_bounds (s : ℕ) (hs : 2 ≤ s) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    (native capacity resource hC hR).2 ≤ workEnvelope s ∧
      usage (native capacity resource hC hR).1.2 ≤ BinaryPRGHeapLowerSourceBound.envelope s := by
  refine ⟨native_work s hs capacity resource hC hR hCapacity hResource,?_⟩
  rw [native_erases]
  exact BinaryPRGHeapLowerSourceBound.nativeWithTrace_usage s hs capacity resource hC hR hCapacity hResource

theorem all_prefix (s : ℕ) (hs : 2 ≤ s) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCapacity : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (native capacity resource hC hR).1.2 steps ≤
      borrowed + BinaryPRGHeapLowerSourceBound.envelope s ∧
    framePeak ((native capacity resource hC hR).1.2.take steps) ≤ BinaryPRGHeapLowerSourceBound.envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (native_bounds s hs capacity resource hC hR hCapacity hResource).2 borrowed steps

end Blotto.BinaryPRGHeapLowerSourceMeasured
