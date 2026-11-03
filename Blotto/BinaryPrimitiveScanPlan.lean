import Blotto.BinaryPackedReadPlan
import Blotto.BinaryInitialScanPlan

/-! Packed read plans feed the existing fractional/scan plan and its actual
emitter. All previous data/trace/comparison/total/emission counters remain exact.
The added field forwards the reached packed-read emissions. -/
namespace Blotto.BinaryPrimitiveScanPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryRationalNormalization
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed pack)
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded block_bound)
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {capacity : Store}

def fractionalAt (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (depth : ℕ) : ((Bool × Plan) × (ℕ × ℕ)) × ℕ :=
  let bidProduced := BinaryPackedReadPlan.readWithEmission bids address.word
  let limitProduced := BinaryPackedReadPlan.readWithEmission (pack limits) address.word
  let bid := bidProduced.1
  let limit := limitProduced.1
  let positive := BinaryRationalComparisonMeasured.traced bid.1.1 BinaryRationalOpcode.zero
  let below := BinaryRationalComparisonMeasured.traced limit.1.1 bid.1.1
  let comparison := positive.2+below.2
  ((((!positive.1.1) && (!below.1.1),.join (.block [.frames (depth+2),.arrayAllocation 16])
    (.join (.shifted (depth+2) bid.1.2) (.join (.shifted (depth+2) limit.1.2)
      (.join (.shifted (depth+2) positive.1.2) (.shifted (depth+2) below.1.2))))),
    (comparison,comparison+bid.2+limit.2+6)),bidProduced.2+limitProduced.2)

theorem fractional_compat (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (depth : ℕ) :
    (fractionalAt limits bids address depth).1 = BinaryInitialScanPlan.fractionalAt limits bids address depth := by
  simp only [fractionalAt,BinaryInitialScanPlan.fractionalAt,BinaryPackedReadPlan.read_compat]

theorem fractional_price (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (depth : ℕ) :
    (fractionalAt limits bids address depth).2 ≤ 25*payload (fractionalAt limits bids address depth).1.1.2 := by
  have hb := BinaryPackedReadPlan.read_emission_bound bids address.word
  have hl := BinaryPackedReadPlan.read_emission_bound (pack limits) address.word
  simp only [fractionalAt,payload,List.length_cons,List.length_nil]
  omega

def scanAt (limits : Stored capacity.tree) (bids : Packed capacity.width) :
    List (Address capacity.width capacity.cap) → ℕ →
      ((List (Address capacity.width capacity.cap) × Plan) × (ℕ × ℕ)) × ℕ
  | [],depth => ((([],.block [.frames (depth+1),.arrayAllocation 8]),(0,1)),0)
  | address::rest,depth =>
      let testedProduced := fractionalAt limits bids address (depth+2)
      let laterProduced := scanAt limits bids rest (depth+2)
      let tested := testedProduced.1
      let later := laterProduced.1
      (((if tested.1.1 then address::later.1.1 else later.1.1,
        .join (.block [.listAllocation (if tested.1.1 then 1 else 0),.frames (depth+2),.arrayAllocation 8])
          (.join tested.1.2 later.1.2)),
        (tested.2.1+later.2.1,tested.2.2+later.2.2+2*(address.word.bits.length+1)+3)),testedProduced.2+laterProduced.2)

theorem scan_compat (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) (depth : ℕ) :
    (scanAt limits bids addresses depth).1 = BinaryInitialScanPlan.scanAt limits bids addresses depth := by
  induction addresses generalizing depth with
  | nil => rfl
  | cons address rest ih =>
      simp only [scanAt,BinaryInitialScanPlan.scanAt,fractional_compat,ih]

theorem scan_price (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) (depth : ℕ) :
    (scanAt limits bids addresses depth).2 ≤ 25*payload (scanAt limits bids addresses depth).1.1.2 := by
  induction addresses generalizing depth with
  | nil => simp only [scanAt,payload,List.length_cons,List.length_nil]; omega
  | cons address rest ih =>
      have hf := fractional_price limits bids address (depth+2)
      have hl := ih (depth+2)
      simp only [scanAt,payload,List.length_cons,List.length_nil]
      omega

def scanWithEmission (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :=
  let produced := scanAt limits bids addresses 0
  (finish produced.1,produced.2)

theorem scanWithEmission_compat (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithEmission limits bids addresses).1 = BinaryInitialScanPlan.scanWithEmission limits bids addresses := by
  simp only [scanWithEmission,scan_compat]
  rfl

theorem scanWithEmission_price (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithEmission limits bids addresses).2 ≤ 25*(scanWithEmission limits bids addresses).1.1.1.2.length := by
  have h := scan_price limits bids addresses 0
  simpa only [scanWithEmission,BinaryNumericalReadbackPlan.finish_record,view,denote_length] using h

end Blotto.BinaryPrimitiveScanPlan
