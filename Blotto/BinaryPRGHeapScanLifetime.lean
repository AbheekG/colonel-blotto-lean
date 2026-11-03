import Blotto.BinaryPRGHeapTraceUsage
import Blotto.BinaryPRGHeapResourceLoop
import Blotto.BinaryQuadraticResourceStateLifetime

/-! Physical fractional tests and active-list rescans consume traced tape
reads and the unchanged exact Boolean comparisons. -/

namespace Blotto.BinaryPRGHeapScanLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed pack)
open BinaryPRGHeapTraceUsage
open BinaryQuadraticResourceStateLifetime (compareWithTrace compareWithTrace_erases compareWithTrace_bounds compareBound compareFrames)
set_option maxHeartbeats 1000000

variable {capacity : Store}

def fractionalWithTrace (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) : Bool × Trace :=
  let bid := BinaryPRGHeapPackedLifetime.readWithTrace bids address.word
  let limit := BinaryPRGHeapPackedLifetime.readWithTrace (pack limits) address.word
  let positive := compareWithTrace bid.1 BinaryRationalOpcode.zero
  let below := compareWithTrace limit.1 bid.1
  ((!positive.1) && (!below.1),wrap 16 2 [bid.2,limit.2,positive.2,below.2])

theorem fractionalWithTrace_erasure (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) :
    (fractionalWithTrace limits bids address).1 =
      (BinaryPRGHeapResourceLoop.fractionalWithWork limits bids address).1 := by
  simp only [fractionalWithTrace,BinaryPRGHeapResourceLoop.fractionalWithWork,
    BinaryPRGHeapPackedLifetime.readWithTrace_erasure,compareWithTrace_erases]
  rfl

def fractionalEnvelope (C H depth W : ℕ) : ℕ :=
  readEnvelope C depth + readEnvelope H depth + 2 * (compareBound W + compareFrames W) + 32

theorem fractionalWithTrace_usage (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (C H W : ℕ)
    (hC : limits.heap.tape.length ≤ C) (hH : bids.heap.tape.length ≤ H) (hW : 1 ≤ W)
    (hBid : width (bids.readWithWork address.word).1 ≤ W)
    (hLimit : width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W) :
    usage (fractionalWithTrace limits bids address).2 ≤ fractionalEnvelope C H capacity.width W := by
  let bid := BinaryPRGHeapPackedLifetime.readWithTrace bids address.word
  let limit := BinaryPRGHeapPackedLifetime.readWithTrace (pack limits) address.word
  have hb := read_usage bids address.word H hH
  have hl := read_usage (pack limits) address.word C hC
  have hbW : width bid.1 ≤ W := by simpa only [bid,BinaryPRGHeapPackedLifetime.readWithTrace_erasure] using hBid
  have hlW : width limit.1 ≤ W := by
    dsimp only [limit]
    rw [BinaryPRGHeapPackedLifetime.readWithTrace_erasure]
    exact hLimit
  have hp := compareWithTrace_bounds bid.1 BinaryRationalOpcode.zero W hbW hW
  have hc := compareWithTrace_bounds limit.1 bid.1 W hlW hbW
  have hWrap := wrap_usage 16 2 [bid.2,limit.2,(compareWithTrace bid.1 BinaryRationalOpcode.zero).2,
    (compareWithTrace limit.1 bid.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  unfold fractionalWithTrace fractionalEnvelope
  change usage (wrap 16 2 [bid.2,limit.2,(compareWithTrace bid.1 BinaryRationalOpcode.zero).2,
    (compareWithTrace limit.1 bid.1).2]) ≤ _
  change usage bid.2 ≤ _ at hb
  change usage limit.2 ≤ _ at hl
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells BinaryQuadraticResourceStateLifetime.cells at *
  omega

def scanWithTrace (limits : Stored capacity.tree) (bids : Packed capacity.width) :
    List (Address capacity.width capacity.cap) → List (Address capacity.width capacity.cap) × Trace
  | [] => ([],wrap 8 1 [])
  | address :: rest =>
      let tested := fractionalWithTrace limits bids address
      let later := scanWithTrace limits bids rest
      (if tested.1 then address :: later.1 else later.1,
        wrapList (if tested.1 then 1 else 0) 8 2 [tested.2,later.2])

theorem scanWithTrace_erasure (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithTrace limits bids addresses).1 =
      (BinaryPRGHeapResourceLoop.scanWithWork limits bids addresses).1 := by
  induction addresses with
  | nil => rfl
  | cons address rest ih => simp only [scanWithTrace,BinaryPRGHeapResourceLoop.scanWithWork,
      fractionalWithTrace_erasure,ih]

def scanEnvelope (C H depth W count : ℕ) : ℕ := count * (fractionalEnvelope C H depth W + 16) + 9

theorem scanWithTrace_usage (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) (C H W : ℕ)
    (hC : limits.heap.tape.length ≤ C) (hH : bids.heap.tape.length ≤ H) (hW : 1 ≤ W)
    (hBid : ∀ address : Address capacity.width capacity.cap,width (bids.readWithWork address.word).1 ≤ W)
    (hLimit : ∀ address : Address capacity.width capacity.cap,width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W) :
    usage (scanWithTrace limits bids addresses).2 ≤ scanEnvelope C H capacity.width W addresses.length := by
  induction addresses with
  | nil => simp [scanWithTrace,scanEnvelope,usage,BinaryPRGHeapPrimitiveLifetime.cells,
      wrap,combine,listCells,arraySlots,framePeak]
  | cons address rest ih =>
      have ht := fractionalWithTrace_usage limits bids address C H W hC hH hW (hBid address) (hLimit address)
      have hw := wrapList_usage
        (if (fractionalWithTrace limits bids address).1 then 1 else 0) 8 2
        [(fractionalWithTrace limits bids address).2,(scanWithTrace limits bids rest).2]
      have hb : (if (fractionalWithTrace limits bids address).1 then 1 else 0) ≤ 1 := by split <;> omega
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      unfold scanWithTrace scanEnvelope
      unfold scanEnvelope at ih
      simp only [List.length_cons]
      nlinarith

end Blotto.BinaryPRGHeapScanLifetime
