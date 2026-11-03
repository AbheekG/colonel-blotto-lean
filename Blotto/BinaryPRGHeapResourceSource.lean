import Blotto.BinaryPRGHeapResourceLoop
import Blotto.BinaryPRGHeapAddressEnumeration
import Blotto.BinaryPRGWordControllerBooleanResourceSource

/-! Original array cells build two retained tape heaps with one Boolean ruler.
A cap-word-only enumerator supplies the initial Boolean identifiers, and an
actual heap scan selects the initial fractional set. Logical trees and the
native certified state occur only in erased type indices and proofs. The
physical source retains its heaps into the recursive resource runner. Final
heap-to-row materialization and whole source/lifetime bounds remain separate. -/

namespace Blotto.BinaryPRGHeapResourceSource
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address State fractional)
open BinaryPRGWordControllerBooleanResourceLoop (Certified)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGWordStoreHeap (Realizes)

variable {n : ℕ}

abbrev capStore (capacity : FixedArrayTable n SignedWord) : Store :=
  BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity

abbrev resStore (capacity resource : FixedArrayTable n SignedWord) : Store :=
  BinaryPRGWordControllerBooleanResourceSource.resourceStore capacity resource

abbrev count (capacity : FixedArrayTable n SignedWord) : n = (capStore capacity).cap.value :=
  BinaryPRGWordControllerBooleanResourceSource.source_count capacity

def initialWithWork (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    (Stored (capStore capacity).tree × Finished (capStore capacity) n (count capacity)) × ℕ :=
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  let limits := BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero ruler capacity.data.toList
  let bids := BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero ruler resource.data.toList
  let capWord : FixedBinaryWord ruler.length := ⟨ruler,rfl⟩
  let ids := BinaryPRGHeapAddressEnumeration.allWithWork capWord
  let retained := BinaryPRGHeapResourceLoop.scanWithWork limits.1 (pack bids.1) ids.1
  let logical := BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR
  let hResource : Realizes bids.1.heap.tape bids.1.root logical.state.resource := bids.1.realizes
  let hActive : retained.1 = logical.state.active := by
    have hPacked : Realizes (pack bids.1).heap.tape (pack bids.1).root logical.state.resource := hResource
    change (BinaryPRGHeapResourceLoop.scanWithWork (capacity := capStore capacity)
      limits.1 (pack bids.1) ids.1).1 = logical.state.active
    rw [BinaryPRGHeapResourceLoop.scanWithWork_value (capacity := capStore capacity)
      limits.1 (pack bids.1) hPacked ids.1]
    exact congrArg (fun addresses => addresses.filter
      (fractional (capStore capacity).tree logical.state.resource))
      (BinaryPRGHeapAddressEnumeration.allWithWork_reference (capStore capacity))
  let physical : BinaryPRGHeapResourceUpdate.Physical logical.state :=
    ⟨⟨bids.1.ruler,bids.1.size,bids.1.heap,bids.1.root,bids.1.valid,hResource⟩,
      retained.1,hActive⟩
  ((limits.1, BinaryPRGHeapResourceLoop.finished logical physical),
    BinaryCarryCounter.countCarryCells capacity.data.toList [] +
      limits.2.work + bids.2.work + ids.2 + retained.2 + 8)

theorem initialWithWork_reference (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    ((initialWithWork capacity resource hC hR).1.2).reference =
      BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR := by
  unfold initialWithWork
  dsimp only
  exact BinaryPRGHeapResourceLoop.finished_reference _ _

def initialWorkEnvelope (capacity resource : FixedArrayTable n SignedWord) : ℕ :=
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  let limits := BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero ruler capacity.data.toList
  let bids := BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero ruler resource.data.toList
  let capWord : FixedBinaryWord ruler.length := ⟨ruler,rfl⟩
  let ids := BinaryPRGHeapAddressEnumeration.allWithWork capWord
  BinaryCarryCounter.countCarryCells capacity.data.toList [] +
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound limits.1.heap.tape.length + 8) +
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound bids.1.heap.tape.length + 8) +
    capWord.value * (20 * (ruler.length + 1) + 4) + 12 * (ruler.length + 1) + 1 +
    BinaryPRGHeapResourceLoop.scanWorkBoundPacked
      (pack limits.1) (pack bids.1) ids.1 + 8

theorem initialWithWork_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initialWithWork capacity resource hC hR).2 ≤
      initialWorkEnvelope capacity resource := by
  let ruler := BinaryCarryCounter.count capacity.data.toList []
  let limits := BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero ruler capacity.data.toList
  let bids := BinaryPRGHeapStoredTree.prepareRulerWithWork BinaryRationalOpcode.zero ruler resource.data.toList
  let capWord : FixedBinaryWord ruler.length := ⟨ruler,rfl⟩
  let ids := BinaryPRGHeapAddressEnumeration.allWithWork capWord
  have hLimits := BinaryPRGHeapStoredTree.prepareRulerWithWork_workBound
    BinaryRationalOpcode.zero ruler capacity.data.toList
  have hBids := BinaryPRGHeapStoredTree.prepareRulerWithWork_workBound
    BinaryRationalOpcode.zero ruler resource.data.toList
  have hIds := BinaryPRGHeapAddressEnumeration.allWithWork_bound capWord
  have hScan := BinaryPRGHeapResourceLoop.scanWithWork_bound (capacity := capStore capacity)
    limits.1 (pack bids.1) ids.1
  change limits.2.work ≤ BinaryPRGWordStoreHeapMachine.nodes ruler.length *
    (BinaryPRGWordStoreHeapMachine.allocationBound limits.1.heap.tape.length + 8) at hLimits
  change bids.2.work ≤ BinaryPRGWordStoreHeapMachine.nodes ruler.length *
    (BinaryPRGWordStoreHeapMachine.allocationBound bids.1.heap.tape.length + 8) at hBids
  change ids.2 ≤ capWord.value * (20 * (ruler.length + 1) + 4) +
    12 * (ruler.length + 1) + 1 at hIds
  change (BinaryPRGHeapResourceLoop.scanWithWork (capacity := capStore capacity)
    limits.1 (pack bids.1) ids.1).2 ≤
    BinaryPRGHeapResourceLoop.scanWorkBoundPacked
      (pack limits.1) (pack bids.1) ids.1 at hScan
  unfold initialWithWork initialWorkEnvelope
  dsimp only
  change BinaryCarryCounter.countCarryCells capacity.data.toList [] +
    limits.2.work + bids.2.work + ids.2 +
    (BinaryPRGHeapResourceLoop.scanWithWork (capacity := capStore capacity)
      limits.1 (pack bids.1) ids.1).2 + 8 ≤
    BinaryCarryCounter.countCarryCells capacity.data.toList [] +
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound limits.1.heap.tape.length + 8) +
    BinaryPRGWordStoreHeapMachine.nodes ruler.length *
      (BinaryPRGWordStoreHeapMachine.allocationBound bids.1.heap.tape.length + 8) +
    capWord.value * (20 * (ruler.length + 1) + 4) + 12 * (ruler.length + 1) + 1 +
    BinaryPRGHeapResourceLoop.scanWorkBoundPacked
      (pack limits.1) (pack bids.1) ids.1 + 8
  omega

def runWithWork (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity) × ℕ :=
  let prepared := initialWithWork capacity resource hC hR
  let completed := BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    prepared.1.2 (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  (completed.1,prepared.2 + completed.2 + 3)

def runWithRetainedCap (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    (FixedBinaryWord (capStore capacity).width ×
      BinaryPRGHeapResourceLoop.Result seed (capStore capacity) n (count capacity)) × ℕ :=
  let prepared := initialWithWork capacity resource hC hR
  let capWord : FixedBinaryWord (capStore capacity).width :=
    ⟨prepared.1.1.ruler,prepared.1.1.size⟩
  let completed := BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    prepared.1.2 (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  ((capWord,completed.1),prepared.2 + completed.2 + 3)

theorem runWithRetainedCap_result (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    ((runWithRetainedCap seed capacity resource hC hR).1.2,
      (runWithRetainedCap seed capacity resource hC hR).2) =
      runWithWork seed capacity resource hC hR := by
  unfold runWithRetainedCap runWithWork
  rfl

theorem runWithRetainedCap_cap (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    (runWithRetainedCap seed capacity resource hC hR).1.1 =
      (capStore capacity).cap := by
  unfold runWithRetainedCap initialWithWork
  rfl

theorem runWithWork_reference (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    (runWithWork seed capacity resource hC hR).1.reference =
      BinaryPRGWordControllerBooleanResourceLoop.run seed (capStore capacity)
        n (count capacity)
        (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
        (BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR)
        (BinaryWordIndexCoinController.zeroIndex seed)
        (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _) := by
  unfold runWithWork
  dsimp only
  rw [BinaryPRGHeapResourceLoop.runWithWork_value,initialWithWork_reference]

theorem runWithWork_original (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j)) :
    BinaryPRGWordControllerBooleanResourceSource.result capacity seed
      ((runWithWork seed capacity resource hC hR).1).reference =
      BinaryPRGWordControllerResource.initialRun seed capacity resource hC hR := by
  rw [runWithWork_reference]
  exact BinaryPRGWordControllerBooleanResourceSource.initialRun_original
    seed capacity resource hC hR

end Blotto.BinaryPRGHeapResourceSource
