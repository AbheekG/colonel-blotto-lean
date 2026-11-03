import Blotto.BinaryPRGHeapRulerLifetime
import Blotto.BinaryPRGHeapEnumerationLifetime
import Blotto.BinaryPRGHeapScanComparisonWork

/-! Original-array initialization consumes one traced ruler and both physical
builds, cap-only enumeration and the actual fractional scan. Array-list copies
and all old build/counter regions stay retained in the source trace. -/

namespace Blotto.BinaryPRGHeapInitialLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address fractional)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceSource (capStore resStore count)
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 1500000

variable {n : ℕ}

def ArraysAt (capacity resource : FixedArrayTable n SignedWord) (ruler : List Bool) : Type :=
  Stored (BinaryPRGWordControllerWordStore.build BinaryRationalOpcode.zero ruler capacity.data.toList).1 ×
    Stored (BinaryPRGWordControllerWordStore.build BinaryRationalOpcode.zero ruler resource.data.toList).1

def arraysWithTrace (capacity resource : FixedArrayTable n SignedWord) :
    (Stored (capStore capacity).tree × Stored (resStore capacity resource).tree) × Trace :=
  let counted := BinaryPRGHeapAllocationLifetime.countWithTrace capacity.data.toList []
  let limits := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero counted.1 capacity.data.toList
  let bids := BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero counted.1 resource.data.toList
  have hRuler : counted.1 = BinaryCarryCounter.count capacity.data.toList [] :=
    (BinaryPRGHeapAllocationLifetime.countWithTrace_erasure capacity.data.toList []).trans
      (BinaryPRGWordStoreHeapMachine.countWithWork_erasure capacity.data.toList [])
  let result : ArraysAt capacity resource counted.1 := (limits.1,bids.1)
  let transported : ArraysAt capacity resource (BinaryCarryCounter.count capacity.data.toList []) := hRuler ▸ result
  (transported,wrapList (3 * n) 64 (3 * n + 4) [counted.2,limits.2,bids.2])

theorem arrays_transport (capacity resource : FixedArrayTable n SignedWord) (ruler original : List Bool)
    (h : ruler = original) :
    (h ▸ ((BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero ruler capacity.data.toList).1,
      (BinaryPRGHeapRulerLifetime.prepareRulerWithTrace BinaryRationalOpcode.zero ruler resource.data.toList).1) :
      ArraysAt capacity resource original) =
    ((BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero original capacity.data.toList).1,
      (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero original resource.data.toList).1) := by
  subst original
  simp only [BinaryPRGHeapRulerLifetime.prepareRulerWithTrace_erasure]
  rfl

theorem arraysWithTrace_erasure (capacity resource : FixedArrayTable n SignedWord) :
    (arraysWithTrace capacity resource).1 =
      ((BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) capacity.data.toList).1,
        (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) resource.data.toList).1) := by
  unfold arraysWithTrace
  exact arrays_transport capacity resource _ _ _

theorem arrays_limits_erasure (capacity resource : FixedArrayTable n SignedWord) :
    (arraysWithTrace capacity resource).1.1 = (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
      (BinaryCarryCounter.count capacity.data.toList []) capacity.data.toList).1 :=
  congrArg Prod.fst (arraysWithTrace_erasure capacity resource)

theorem arrays_bids_erasure (capacity resource : FixedArrayTable n SignedWord) :
    (arraysWithTrace capacity resource).1.2 = (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
      (BinaryCarryCounter.count capacity.data.toList []) resource.data.toList).1 :=
  congrArg Prod.snd (arraysWithTrace_erasure capacity resource)

def initialWithTrace (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × Trace :=
  let arrays := arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,arrays,arrays_limits_erasure]
    rfl
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  let addresses : List (Address (capStore capacity).width (capStore capacity).cap) := hCap ▸ ids.1
  let measured := BinaryPRGHeapScanComparisonWork.scanWithFullWork arrays.1.1 (pack arrays.1.2) addresses
  let retained := measured.1
  let logical := BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR
  have hResource : BinaryPRGWordStoreHeap.Realizes arrays.1.2.heap.tape arrays.1.2.root logical.state.resource := arrays.1.2.realizes
  have hActive : retained.1 = logical.state.active := by
    dsimp only [retained,addresses]
    rw [BinaryPRGHeapScanComparisonWork.scanWithFullWork_erases]
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
    dsimp only [addresses,ids]
    rw [hIds]
    rfl
  let physical : BinaryPRGHeapResourceUpdate.Physical logical.state :=
    ⟨⟨arrays.1.2.ruler,arrays.1.2.size,arrays.1.2.heap,arrays.1.2.root,arrays.1.2.valid,hResource⟩,retained.1,hActive⟩
  ((arrays.1.1,BinaryPRGHeapResourceLoop.finished logical physical),wrap 32 2 [arrays.2,ids.2,retained.2])

/-- The comparison ledger of the physical scan selected by `initialWithTrace`.
It is exposed separately because the existing initializer result carries only
its resource state and retained-storage trace. -/
def initialComparisonWork (capacity resource : FixedArrayTable n SignedWord) : ℕ :=
  let arrays := arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,arrays,arrays_limits_erasure]
    rfl
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  (BinaryPRGHeapScanComparisonWork.scanWithFullWork arrays.1.1 (pack arrays.1.2) (hCap ▸ ids.1)).2.1

/-- The complete physical lookup, comparison and list-control charge of the
initial scan selected by `initialWithTrace`. -/
def initialPhysicalScanWork (capacity resource : FixedArrayTable n SignedWord) : ℕ :=
  let arrays := arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (capStore capacity).width := ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,arrays,arrays_limits_erasure]
    rfl
  let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
  (BinaryPRGHeapScanComparisonWork.scanWithFullWork arrays.1.1 (pack arrays.1.2) (hCap ▸ ids.1)).2.2

theorem initialPhysicalScanWork_plus_control_le_initialWithWork
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    initialPhysicalScanWork capacity resource + (2*n+5) ≤
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 := by
  let arrays := arraysWithTrace capacity resource
  let capWord : FixedBinaryWord (capStore capacity).width :=
    ⟨arrays.1.1.ruler,arrays.1.1.size⟩
  have hCap : capWord = (capStore capacity).cap := by
    simp only [capWord,arrays,arrays_limits_erasure]
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
  have hArrays := arraysWithTrace_erasure capacity resource
  have hScan : initialPhysicalScanWork capacity resource =
      (BinaryPRGHeapResourceLoop.scanWithWork
        (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) capacity.data.toList).1
        (pack (BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero
          (BinaryCarryCounter.count capacity.data.toList []) resource.data.toList).1)
        (BinaryPRGWordControllerBooleanResourceInitial.allAddresses
          (capStore capacity))).2 := by
    unfold initialPhysicalScanWork
    dsimp only
    rw [BinaryPRGHeapScanComparisonWork.scanWithFullWork_charge]
    rw [hIds]
    rw [hArrays]
  rw [hScan]
  unfold BinaryPRGHeapResourceSource.initialWithWork
  dsimp only
  have hNativeIds :
      (BinaryPRGHeapAddressEnumeration.allWithWork
        (⟨BinaryCarryCounter.count capacity.data.toList [],rfl⟩ :
          FixedBinaryWord (BinaryCarryCounter.count capacity.data.toList []).length)).1 =
        BinaryPRGWordControllerBooleanResourceInitial.allAddresses
          (capStore capacity) := by
    exact BinaryPRGHeapAddressEnumeration.allWithWork_reference (capStore capacity)
  rw [hNativeIds]
  have hCounter : n ≤ BinaryCarryCounter.countCarryCells capacity.data.toList [] := by
    simpa only [Array.length_toList,capacity.size] using
      BinaryCarryCounter.countCarryCells_ge_length capacity.data.toList []
  have hEnum := BinaryPRGHeapAddressEnumeration.allWithWork_lower
    (⟨BinaryCarryCounter.count capacity.data.toList [],rfl⟩ :
      FixedBinaryWord (BinaryCarryCounter.count capacity.data.toList []).length)
  have hCountValue :
      (⟨BinaryCarryCounter.count capacity.data.toList [],rfl⟩ :
        FixedBinaryWord (BinaryCarryCounter.count capacity.data.toList []).length).value = n := by
    change BinaryCarryCounter.value (BinaryCarryCounter.count capacity.data.toList []) = n
    rw [BinaryCarryCounter.count_value]
    simp [BinaryCarryCounter.value,Array.length_toList,capacity.size]
    rfl
  omega

theorem initialPhysicalScanWork_le_initialWithWork
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    initialPhysicalScanWork capacity resource ≤
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).2 := by
  have h := initialPhysicalScanWork_plus_control_le_initialWithWork capacity resource hC hR
  omega

theorem initialWithTrace_measured_scan (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    let arrays := arraysWithTrace capacity resource
    let capWord : FixedBinaryWord (capStore capacity).width := ⟨arrays.1.1.ruler,arrays.1.1.size⟩
    let hCap : capWord = (capStore capacity).cap := by
      simp only [capWord,arrays,arrays_limits_erasure]
      rfl
    let ids := BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace capWord
    let measured := BinaryPRGHeapScanComparisonWork.scanWithFullWork
      arrays.1.1 (pack arrays.1.2) (hCap ▸ ids.1)
    (initialWithTrace capacity resource hC hR).2 =
      wrap 32 2 [arrays.2,ids.2,measured.1.2] ∧
    initialComparisonWork capacity resource = measured.2.1 ∧
    initialPhysicalScanWork capacity resource = measured.2.2 := by
  exact ⟨rfl,rfl,rfl⟩

theorem initialWithTrace_reference (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initialWithTrace capacity resource hC hR).1.2.reference =
      BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR := by
  unfold initialWithTrace
  dsimp only
  exact BinaryPRGHeapResourceLoop.finished_reference _ _

theorem finished_data_ext {capacity : Store} {m : ℕ} {hCount : m = capacity.cap.value}
    (first second : Finished capacity m hCount) (hRuler : first.ruler = second.ruler)
    (hHeap : first.heap = second.heap) (hRoot : first.root = second.root) (hActive : first.active = second.active) :
    first = second := by
  cases first
  cases second
  cases hRuler
  cases hHeap
  cases hRoot
  cases hActive
  rfl

theorem initialWithTrace_erasure (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initialWithTrace capacity resource hC hR).1 =
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1 := by
  apply Prod.ext
  · exact arrays_limits_erasure capacity resource
  · apply finished_data_ext
    · exact congrArg (fun data => data.ruler) (arrays_bids_erasure capacity resource)
    · exact congrArg (fun data => data.heap) (arrays_bids_erasure capacity resource)
    · exact congrArg (fun data => data.root) (arrays_bids_erasure capacity resource)
    · let fresh := (initialWithTrace capacity resource hC hR).1.2
      let previous := (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.2
      have hn := congrArg (fun state => state.state.active) (initialWithTrace_reference capacity resource hC hR)
      have ho := congrArg (fun state => state.state.active)
        (BinaryPRGHeapResourceSource.initialWithWork_reference capacity resource hC hR)
      exact fresh.certified.choose_spec.2.trans (hn.trans (ho.symm.trans previous.certified.choose_spec.2.symm))

end Blotto.BinaryPRGHeapInitialLifetime
