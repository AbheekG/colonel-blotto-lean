import Blotto.BinaryInitialScanPlan
import Blotto.BinaryPhysicalHeapInitialLifetime
import Blotto.BinarySeedWrapperEmission

/-! Actual raw-build and certified-array wrappers use returned trace emitters.
The array initializer consumes the actual planned scan once. Prior complete
records are exact; raw build/read/enumeration leaves and native prices retain
explicit boundaries. -/
namespace Blotto.BinaryInitialWrapperEmission
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceSource (capStore resStore count)
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {n : ℕ}

def listThree (allocated slots frames : ℕ) (first second third : Trace) : Trace × ℕ :=
  let emitted := emitFull (.join (.block [.listAllocation allocated,.frames frames,.arrayAllocation slots])
    (.join (.shifted 2 first) (.join (.shifted 2 second) (.shifted 2 third)))) []
  (emitted.1.1,emitted.1.2+emitted.2)

theorem listThree_trace (allocated slots frames : ℕ) (first second third : Trace) :
    (listThree allocated slots frames first second third).1 = wrapList allocated slots frames [first,second,third] := by
  simp only [listThree,emitFull_erases,emit_data,denote,List.append_nil,wrapList,wrap,combine]
  rfl

theorem listThree_work (allocated slots frames : ℕ) (first second third : Trace) :
    (listThree allocated slots frames first second third).2 = 5*first.length+5*second.length+5*third.length+26 := by
  simp only [listThree,emitFull_erases,emit_work,emitFull_shifts,payload,nodes,shiftCount,List.length_cons,List.length_nil]
  omega

theorem listThree_length (allocated slots frames : ℕ) (first second third : Trace) :
    (listThree allocated slots frames first second third).1.length = first.length+second.length+third.length+3 := by
  simp only [listThree,emitFull_erases,emit_length,payload,List.length_cons,List.length_nil]
  omega

def rawArraysWithEmission (capacity resource : List SignedWord) :=
  let counted := BinaryPRGHeapAllocationLifetime.countWithTrace capacity []
  let limits := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero counted.1 capacity
  let bids := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero counted.1 resource
  let emitted := listThree (3*capacity.length) 64 (3*capacity.length+4) counted.2 limits.2 bids.2
  (((⟨counted.1,(limits.1,bids.1)⟩ : Σ ruler, BinaryPhysicalHeapInputLifetime.RawArraysAt capacity resource ruler),emitted.1),emitted.2)

theorem rawArraysWithEmission_compat (capacity resource : List SignedWord) :
    (rawArraysWithEmission capacity resource).1 = BinaryPhysicalHeapInputLifetime.rawArraysWithTrace capacity resource := by
  simp only [rawArraysWithEmission,BinaryPhysicalHeapInputLifetime.rawArraysWithTrace,listThree_trace]

theorem rawArraysWithEmission_bound (capacity resource : List SignedWord) :
    (rawArraysWithEmission capacity resource).2 ≤ 5*(rawArraysWithEmission capacity resource).1.2.length+26 := by
  simp only [rawArraysWithEmission,listThree_work,listThree_length]
  omega

theorem three_plus_bound (first second third : Trace) (extra : ℕ) (h : extra ≤ 25*third.length+5) :
    extra+(BinarySeedWrapperEmission.three 32 2 first second third).2 ≤
      30*(BinarySeedWrapperEmission.three 32 2 first second third).1.length+27 := by
  rw [BinarySeedWrapperEmission.three_work,BinarySeedWrapperEmission.three_length]
  omega

def initialFromArraysWithTraceAndWork
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :=
  let arrays :
      (Stored (capStore capacity).tree ×
        Stored (resStore capacity resource).tree) × Trace :=
    (built,builtTrace)
  let capWord : FixedBinaryWord (capStore capacity).width :=
    ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,arrays,hBuilt,
      BinaryPRGHeapInitialLifetime.arrays_limits_erasure]
    rfl
  let ids := (BinaryHeapEnumerationWidthMeasured.allFromBits capWord).1
  let addresses : List (Address (capStore capacity).width (capStore capacity).cap) :=
    hCap ▸ ids.1
  let produced := BinaryInitialScanPlan.scanWithEmission
    arrays.1.1 (pack arrays.1.2) addresses
  let measured := produced.1
  let retained := measured.1
  let logical := BinaryPRGWordControllerBooleanResourceSource.initial
    capacity resource hC hR
  have hResource : BinaryPRGWordStoreHeap.Realizes
      arrays.1.2.heap.tape arrays.1.2.root logical.state.resource :=
    arrays.1.2.realizes
  have hActive : retained.1 = logical.state.active := by
    dsimp only [retained,measured,produced,addresses]
    rw [BinaryInitialScanPlan.scanWithEmission_compat,BinaryHeapScanMeasured.scan_trace]
    rw [BinaryPRGHeapScanLifetime.scanWithTrace_erasure]
    rw [BinaryPRGHeapResourceLoop.scanWithWork_value arrays.1.1
      (pack arrays.1.2) hResource]
    have hIdsGeneral : ∀ (word : FixedBinaryWord (capStore capacity).width)
        (h : word = (capStore capacity).cap),
        (h ▸ (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace word).1) =
          BinaryPRGWordControllerBooleanResourceInitial.allAddresses
            (capStore capacity) := by
      intro word h
      subst word
      rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure]
      exact BinaryPRGHeapAddressEnumeration.allWithWork_reference
        (capStore capacity)
    have hIds := hIdsGeneral capWord hCap
    dsimp only [addresses,ids]
    rw [BinaryHeapEnumerationWidthMeasured.allFromBits_erases,hIds]
    rfl
  let physical : BinaryPRGHeapResourceUpdate.Physical logical.state :=
    ⟨⟨arrays.1.2.ruler,arrays.1.2.size,arrays.1.2.heap,
      arrays.1.2.root,arrays.1.2.valid,hResource⟩,
      retained.1,hActive⟩
  let emitted := BinarySeedWrapperEmission.three 32 2 arrays.2 ids.2 retained.2
  ((((arrays.1.1,BinaryPRGHeapResourceLoop.finished logical physical),emitted.1),measured.2.2),produced.2+emitted.2)

theorem initialFromArrays_compat
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).1 =
      BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace := by
  simp only [initialFromArraysWithTraceAndWork,BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTraceAndWork,
    BinaryInitialScanPlan.scanWithEmission_compat,BinarySeedWrapperEmission.three_trace]

theorem initialFromArrays_bound
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).2 ≤
      30*(initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).1.1.2.length+27 := by
  unfold initialFromArraysWithTraceAndWork
  dsimp only
  apply three_plus_bound
  exact BinaryInitialScanPlan.scanWithEmission_bound _ _ _

theorem initialFromArrays_built_length
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (built : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource
      (BinaryCarryCounter.count capacity.data.toList []))
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1)
    (builtTrace : Trace) :
    builtTrace.length ≤ (initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).1.1.2.length := by
  simp only [initialFromArraysWithTraceAndWork,BinarySeedWrapperEmission.three_length]
  omega

end Blotto.BinaryInitialWrapperEmission
