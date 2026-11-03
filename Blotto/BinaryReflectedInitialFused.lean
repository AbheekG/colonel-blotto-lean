import Blotto.BinaryHeapConstructionPlan
import Blotto.BinaryHeapScanMeasured
import Blotto.BinaryPRGHeapInitialLifetime
import Blotto.BinaryPhysicalHeapInitialLifetime

/-! One actual counter and two returned heap builders supply both old array
trace and build charge. The carry potential recovers the old carry-cell field
from the actual returned ruler; no second counting recursion runs. One actual
measured enumeration/scan then supplies the complete old initializer record. -/
namespace Blotto.BinaryReflectedInitialFused
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceSource (capStore resStore count)
open BinaryPRGHeapPackedStore (pack)
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {n : ℕ}

theorem carry_potential {α : Type*} (items : List α) :
    2*items.length-BinaryCarryCounter.ones (BinaryCarryCounter.count items []) =
      BinaryCarryCounter.countCarryCells items [] := by
  have h := BinaryCarryCounter.count_potential items ([] : List Bool)
  simp only [BinaryCarryCounter.ones] at h
  omega

def arrays (capacity resource : FixedArrayTable n SignedWord) :
    ((Stored (capStore capacity).tree × Stored (resStore capacity resource).tree) × Trace) × ℕ :=
  let capacityWords := capacity.data.toList
  let resourceWords := resource.data.toList
  let counted := BinaryHeapConstructionPlan.countWithEmission capacityWords []
  let limits := BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 capacityWords
  let bids := BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero counted.1.1.1 resourceWords
  have hRuler : counted.1.1.1 = BinaryCarryCounter.count capacity.data.toList [] := by
    rw [BinaryHeapConstructionPlan.count_value,BinaryPRGHeapAllocationLifetime.countWithTrace_erasure,
      BinaryPRGWordStoreHeapMachine.countWithWork_erasure]
  let result : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource counted.1.1.1 := (limits.1.1.1,bids.1.1.1)
  let transported : BinaryPRGHeapInitialLifetime.ArraysAt capacity resource (BinaryCarryCounter.count capacity.data.toList []) :=
    hRuler ▸ result
  let emitted := BinaryInitialWrapperEmission.listThree (3*capacityWords.length) 64 (3*capacityWords.length+4)
    counted.1.1.2 limits.1.1.2 bids.1.1.2
  ((transported,emitted.1),(2*capacityWords.length-BinaryCarryCounter.ones counted.1.1.1)+limits.1.2.work+bids.1.2.work)

theorem arrays_transport (capacity resource : FixedArrayTable n SignedWord) (ruler original : List Bool)
    (h : ruler = original) :
    (h ▸ ((BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero ruler capacity.data.toList).1.1.1,
      (BinaryHeapConstructionPlan.prepareWithEmission BinaryRationalOpcode.zero ruler resource.data.toList).1.1.1) :
      BinaryPRGHeapInitialLifetime.ArraysAt capacity resource original) =
    ((BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero original capacity.data.toList).1,
      (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero original resource.data.toList).1) := by
  subst original
  simp only [BinaryHeapConstructionPlan.prepare_compat,BinaryHeapConstructionPlan.prepareReference,
    BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure]
  rfl

theorem arrays_previous (capacity resource : FixedArrayTable n SignedWord) :
    (arrays capacity resource).1 = BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource := by
  apply Prod.ext
  · trans ((BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) capacity.data.toList).1,
        (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) resource.data.toList).1)
    · unfold arrays
      exact arrays_transport capacity resource _ _ _
    · exact (BinaryPRGHeapInitialLifetime.arraysWithTrace_erasure capacity resource).symm
  · simp only [arrays,BinaryHeapConstructionPlan.count_compat,BinaryHeapConstructionPlan.prepare_compat,
      BinaryHeapConstructionPlan.prepareReference,BinaryInitialWrapperEmission.listThree_trace,
      Array.length_toList,capacity.size,BinaryPRGHeapInitialLifetime.arraysWithTrace]
    rw [BinaryHeapConstructionPlan.count_value]

theorem arrays_work (capacity resource : FixedArrayTable n SignedWord) :
    (arrays capacity resource).2 = BinaryCarryCounter.countCarryCells capacity.data.toList []+
      (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
        (BinaryCarryCounter.count capacity.data.toList []) capacity.data.toList).2.work+
      (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
        (BinaryCarryCounter.count capacity.data.toList []) resource.data.toList).2.work := by
  simp only [arrays,BinaryHeapConstructionPlan.count_compat,BinaryHeapConstructionPlan.prepare_compat,
    BinaryHeapConstructionPlan.prepareReference,BinaryPRGHeapAllocationLifetime.countWithTrace_erasure,
    BinaryPRGWordStoreHeapMachine.countWithWork_erasure,carry_potential]
  rw [BinaryHeapConstructionPlan.count_value,BinaryPRGHeapAllocationLifetime.countWithTrace_erasure,
    BinaryPRGWordStoreHeapMachine.countWithWork_erasure]

theorem arrays_limits (capacity resource : FixedArrayTable n SignedWord) :
    (arrays capacity resource).1.1.1 = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1.1 :=
  congrArg (fun out => out.1.1) (arrays_previous capacity resource)

def fromArrays (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (built : Stored (capStore capacity).tree × Stored (resStore capacity resource).tree)
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1) (builtTrace : Trace) :
    ((Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace) × (ℕ × ℕ) :=
  let arrays := (built,builtTrace)
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,arrays,hBuilt,BinaryPRGHeapInitialLifetime.arrays_limits_erasure]
    rfl
  let enumerated := BinaryHeapEnumerationWidthMeasured.allFromBits capWord
  let ids := enumerated.1
  let addresses : List (Address (capStore capacity).width (capStore capacity).cap) := hCap ▸ ids.1
  let measured := BinaryHeapScanMeasured.scan arrays.1.1 (pack arrays.1.2) addresses
  let retained := measured.1
  let logical := BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR
  have hResource : BinaryPRGWordStoreHeap.Realizes arrays.1.2.heap.tape arrays.1.2.root logical.state.resource := arrays.1.2.realizes
  have hActive : retained.1 = logical.state.active := by
    dsimp only [retained,measured,addresses]
    rw [BinaryHeapScanMeasured.scan_trace]
    rw [BinaryPRGHeapScanLifetime.scanWithTrace_erasure]
    rw [BinaryPRGHeapResourceLoop.scanWithWork_value arrays.1.1 (pack arrays.1.2) hResource]
    have hIdsGeneral : ∀ (word : FixedBinaryWord (capStore capacity).width) (h : word = (capStore capacity).cap),
        (h ▸ (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace word).1) =
          BinaryPRGWordControllerBooleanResourceInitial.allAddresses (capStore capacity) := by
      intro word h
      subst word
      rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure]
      exact BinaryPRGHeapAddressEnumeration.allWithWork_reference (capStore capacity)
    have hIds := hIdsGeneral capWord hCap
    dsimp only [addresses,ids,enumerated]
    rw [BinaryHeapEnumerationWidthMeasured.allFromBits_erases,hIds]
    rfl
  let physical : BinaryPRGHeapResourceUpdate.Physical logical.state :=
    ⟨⟨arrays.1.2.ruler,arrays.1.2.size,arrays.1.2.heap,arrays.1.2.root,arrays.1.2.valid,hResource⟩,retained.1,hActive⟩
  (((arrays.1.1,BinaryPRGHeapResourceLoop.finished logical physical),wrap 32 2 [arrays.2,ids.2,retained.2]),
    (enumerated.2,measured.2.2))


theorem fromArrays_previous (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (built : Stored (capStore capacity).tree × Stored (resStore capacity resource).tree)
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1) (builtTrace : Trace) :
    (fromArrays capacity resource hC hR built hBuilt builtTrace).1 =
      (BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTraceAndWork capacity resource hC hR built hBuilt builtTrace).1 := by
  rw [BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTraceAndWork_eq_reference capacity resource hC hR built hBuilt builtTrace]
  unfold fromArrays BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTraceAndWorkReference
  simp only [BinaryHeapEnumerationWidthMeasured.allFromBits_erases,BinaryHeapScanMeasured.scan_erases (capacity := capStore capacity)]

theorem fromArrays_work (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (built : Stored (capStore capacity).tree × Stored (resStore capacity resource).tree)
    (hBuilt : built = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1) (builtTrace : Trace) :
    (fromArrays capacity resource hC hR built hBuilt builtTrace).2 =
      ((BinaryPRGHeapAddressEnumeration.allWithWork (capStore capacity).cap).2,
        BinaryPRGHeapInitialLifetime.initialPhysicalScanWork capacity resource) := by
  apply Prod.ext
  · change (BinaryHeapEnumerationWidthMeasured.allFromBits
      (⟨built.1.ruler,built.1.size⟩ : FixedBinaryWord (capStore capacity).width)).2 = _
    rw [BinaryHeapEnumerationWidthMeasured.allFromBits_work]
    have hCap : (⟨built.1.ruler,built.1.size⟩ : FixedBinaryWord (capStore capacity).width) = (capStore capacity).cap := by
      simp only [hBuilt,BinaryPRGHeapInitialLifetime.arrays_limits_erasure]
      rfl
    rw [hCap]
  · exact BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTraceAndWork_charge capacity resource hC hR built hBuilt builtTrace

def initial (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    ((Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace) × ℕ :=
  let built := arrays capacity resource
  have hBuilt : built.1.1 = (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).1 :=
    congrArg Prod.fst (arrays_previous capacity resource)
  let prepared := fromArrays capacity resource hC hR built.1.1 hBuilt built.1.2
  (prepared.1,built.2+prepared.2.1+prepared.2.2+8)

theorem initial_previous (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initial capacity resource hC hR).1 = BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR := by
  unfold initial
  dsimp only
  rw [fromArrays_previous]
  apply Prod.ext
  · exact BinaryPhysicalHeapInitialLifetime.initialFromArrays_erasure capacity resource hC hR _ _ _
  · have hTrace := congrArg Prod.snd (arrays_previous capacity resource)
    change (BinaryPhysicalHeapInitialLifetime.initialFromArraysWithTrace capacity resource hC hR _ _ _).2 = _
    rw [hTrace]
    exact BinaryPhysicalHeapInitialLifetime.initialFromArrays_trace capacity resource hC hR _ _

theorem scan_work (capacity resource : FixedArrayTable n SignedWord) :
    BinaryPRGHeapInitialLifetime.initialPhysicalScanWork capacity resource =
      (BinaryPRGHeapResourceLoop.scanWithWork
        (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) capacity.data.toList).1
        (pack (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) resource.data.toList).1)
        (BinaryPRGWordControllerBooleanResourceInitial.allAddresses (capStore capacity))).2 := by
  let arrays := BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (capStore capacity).width :=
    ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,arrays,BinaryPRGHeapInitialLifetime.arrays_limits_erasure]
    rfl
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  have hIdsGeneral : ∀ (word : FixedBinaryWord (capStore capacity).width)
      (h : word = (capStore capacity).cap),
      (h ▸ (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace word).1) =
        BinaryPRGWordControllerBooleanResourceInitial.allAddresses
          (capStore capacity) := by
    intro word h
    subst word
    rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_erasure]
    exact BinaryPRGHeapAddressEnumeration.allWithWork_reference (capStore capacity)
  have hIds : (hCap ▸ ids.1) =
      BinaryPRGWordControllerBooleanResourceInitial.allAddresses (capStore capacity) := by
    exact hIdsGeneral capWord hCap
  have hArrays := BinaryPRGHeapInitialLifetime.arraysWithTrace_erasure capacity resource
  have hScan : BinaryPRGHeapInitialLifetime.initialPhysicalScanWork capacity resource =
      (BinaryPRGHeapResourceLoop.scanWithWork
        (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) capacity.data.toList).1
        (pack (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) resource.data.toList).1)
        (BinaryPRGWordControllerBooleanResourceInitial.allAddresses
          (capStore capacity))).2 := by
    unfold BinaryPRGHeapInitialLifetime.initialPhysicalScanWork
    dsimp only
    rw [BinaryPRGHeapScanComparisonWork.scanWithFullWork_charge]
    rw [hIds]
    rw [hArrays]
  exact hScan

theorem initial_work (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initial capacity resource hC hR).2 = (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 := by
  simp only [initial,fromArrays_work,arrays_work]
  rw [scan_work]
  unfold BinaryPRGHeapResourceSource.initialWithWork
  dsimp only
  have hNativeIds :
      (BinaryPRGHeapAddressEnumeration.allWithWork
        (⟨BinaryCarryCounter.count capacity.data.toList [],rfl⟩ :
          FixedBinaryWord (BinaryCarryCounter.count capacity.data.toList []).length)).1 =
        BinaryPRGWordControllerBooleanResourceInitial.allAddresses (capStore capacity) := by
    exact BinaryPRGHeapAddressEnumeration.allWithWork_reference (capStore capacity)
  rw [hNativeIds]
  rfl

theorem initial_record (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    initial capacity resource hC hR =
      (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR,
        (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2) :=
  Prod.ext (initial_previous capacity resource hC hR) (initial_work capacity resource hC hR)

end Blotto.BinaryReflectedInitialFused
