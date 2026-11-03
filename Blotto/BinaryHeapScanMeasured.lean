import Blotto.BinaryHeapPackedReadMeasured
import Blotto.BinaryRationalComparisonMeasured
import Blotto.BinaryPRGHeapScanComparisonWork

/-! The actual two packed reads and two rational comparisons feed the reached
fractional decision and both old scan ledgers. No old physical read-work or
rational comparison-work/storage producer is replayed in these bodies. The
full old value/trace/comparison-work/total-work record is exact; native observer
arithmetic, reference/ownership and allocator/GC semantics remain separate. -/
namespace Blotto.BinaryHeapScanMeasured
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed pack)
set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {capacity : Store}

def fractional (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) : (Bool × Trace) × (ℕ × ℕ) :=
  let bid := BinaryHeapPackedReadMeasured.read bids address.word
  let limit := BinaryHeapPackedReadMeasured.read (pack limits) address.word
  let positive := BinaryRationalComparisonMeasured.traced bid.1.1 BinaryRationalOpcode.zero
  let below := BinaryRationalComparisonMeasured.traced limit.1.1 bid.1.1
  let comparison := positive.2+below.2
  (((!positive.1.1) && (!below.1.1),wrap 16 2 [bid.1.2,limit.1.2,positive.1.2,below.1.2]),
    (comparison,comparison+bid.2+limit.2+6))

theorem fractional_erases (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) :
    fractional limits bids address =
      BinaryPRGHeapScanComparisonWork.fractionalWithFullWork limits bids address := by
  apply Prod.ext
  · simp only [fractional,BinaryPRGHeapScanComparisonWork.fractionalWithFullWork,
      BinaryPRGHeapScanComparisonWork.fractionalWithWork,
      BinaryRationalComparisonMeasured.traced_erases,BinaryHeapPackedReadMeasured.read_erases]
  · simp only [fractional,BinaryPRGHeapScanComparisonWork.fractionalWithFullWork,
      BinaryPRGHeapScanComparisonWork.fractionalWithWork,
      BinaryRationalComparisonMeasured.traced_work,BinaryHeapPackedReadMeasured.read_work,
      BinaryHeapPackedReadMeasured.read_data,BinaryPRGHeapPackedLifetime.readWithTrace_erasure]
    rfl

theorem fractional_trace (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) :
    (fractional limits bids address).1 = BinaryPRGHeapScanLifetime.fractionalWithTrace limits bids address := by
  rw [fractional_erases,BinaryPRGHeapScanComparisonWork.fractionalWithFullWork_erases]

theorem fractional_work (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) :
    (fractional limits bids address).2.2 = (BinaryPRGHeapResourceLoop.fractionalWithWork limits bids address).2 := by
  rw [fractional_erases,BinaryPRGHeapScanComparisonWork.fractionalWithFullWork_charge]

def scan (limits : Stored capacity.tree) (bids : Packed capacity.width) :
    List (Address capacity.width capacity.cap) →
      (List (Address capacity.width capacity.cap) × Trace) × (ℕ × ℕ)
  | [] => (([],wrap 8 1 []),(0,1))
  | address::rest =>
      let tested := fractional limits bids address
      let later := scan limits bids rest
      ((if tested.1.1 then address::later.1.1 else later.1.1,
        wrapList (if tested.1.1 then 1 else 0) 8 2 [tested.1.2,later.1.2]),
        (tested.2.1+later.2.1,tested.2.2+later.2.2+2*(address.word.bits.length+1)+3))

theorem scan_erases (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    scan limits bids addresses = BinaryPRGHeapScanComparisonWork.scanWithFullWork limits bids addresses := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [scan,BinaryPRGHeapScanComparisonWork.scanWithFullWork,fractional_erases,ih]

theorem scan_trace (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scan limits bids addresses).1 = BinaryPRGHeapScanLifetime.scanWithTrace limits bids addresses := by
  rw [scan_erases,BinaryPRGHeapScanComparisonWork.scanWithFullWork_erases]

theorem scan_comparison (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scan limits bids addresses).2.1 = (BinaryPRGHeapScanComparisonWork.scanWithWork limits bids addresses).2 := by
  rw [scan_erases,BinaryPRGHeapScanComparisonWork.scanWithFullWork_comparison]

theorem scan_work (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scan limits bids addresses).2.2 = (BinaryPRGHeapResourceLoop.scanWithWork limits bids addresses).2 := by
  rw [scan_erases,BinaryPRGHeapScanComparisonWork.scanWithFullWork_charge]

theorem scan_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scan limits bids addresses).2.2 ≤ BinaryPRGHeapResourceLoop.scanWorkBound limits bids addresses := by
  rw [scan_erases]
  exact BinaryPRGHeapScanComparisonWork.scanWithFullWork_bound limits bids addresses

end Blotto.BinaryHeapScanMeasured
