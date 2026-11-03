import Blotto.BinaryNumericalReadbackPlan
import Blotto.BinaryHeapScanMeasured

/-! Actual packed reads/comparisons feed fractional decisions and active-list
construction while scan joins remain a plan. One final emitter preserves both
old scan charges. Read/comparison leaves and native execution remain separate. -/
namespace Blotto.BinaryInitialScanPlan
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
    (address : Address capacity.width capacity.cap) (depth : ℕ) : (Bool × Plan) × (ℕ × ℕ) :=
  let bid := BinaryHeapPackedReadMeasured.read bids address.word
  let limit := BinaryHeapPackedReadMeasured.read (pack limits) address.word
  let positive := BinaryRationalComparisonMeasured.traced bid.1.1 BinaryRationalOpcode.zero
  let below := BinaryRationalComparisonMeasured.traced limit.1.1 bid.1.1
  let comparison := positive.2+below.2
  (((!positive.1.1) && (!below.1.1),.join (.block [.frames (depth+2),.arrayAllocation 16])
    (.join (.shifted (depth+2) bid.1.2) (.join (.shifted (depth+2) limit.1.2)
      (.join (.shifted (depth+2) positive.1.2) (.shifted (depth+2) below.1.2))))),
    (comparison,comparison+bid.2+limit.2+6))

theorem fractional_refines (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (depth : ℕ) :
    view (fractionalAt limits bids address depth) = offset depth (BinaryHeapScanMeasured.fractional limits bids address) := by
  simp only [fractionalAt,BinaryHeapScanMeasured.fractional,view,offset,denote,wrap,combine,
    List.append_nil,under_append,under_compose]
  rfl

theorem fractional_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (address : Address capacity.width capacity.cap) (depth : ℕ) : Bounded (fractionalAt limits bids address depth).1.2 := by
  simp only [Bounded,fractionalAt,nodes,payload,List.length_cons,List.length_nil]
  omega

def scanAt (limits : Stored capacity.tree) (bids : Packed capacity.width) :
    List (Address capacity.width capacity.cap) → ℕ →
      (List (Address capacity.width capacity.cap) × Plan) × (ℕ × ℕ)
  | [],depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),(0,1))
  | address::rest,depth =>
      let tested := fractionalAt limits bids address (depth+2)
      let later := scanAt limits bids rest (depth+2)
      ((if tested.1.1 then address::later.1.1 else later.1.1,
        .join (.block [.listAllocation (if tested.1.1 then 1 else 0),.frames (depth+2),.arrayAllocation 8])
          (.join tested.1.2 later.1.2)),
        (tested.2.1+later.2.1,tested.2.2+later.2.2+2*(address.word.bits.length+1)+3))

theorem scan_refines (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) (depth : ℕ) :
    view (scanAt limits bids addresses depth) = offset depth (BinaryHeapScanMeasured.scan limits bids addresses) := by
  induction addresses generalizing depth with
  | nil => rfl
  | cons address rest ih =>
      have hf := fractional_refines limits bids address (depth+2)
      have hl := ih (depth+2)
      simp only [scanAt,BinaryHeapScanMeasured.scan,view,offset,denote,
        data_refines hf,trace_refines hf,charge_refines hf,data_refines hl,trace_refines hl,charge_refines hl,
        wrapList,wrap,combine,List.append_nil,under_append,under_compose]
      rfl

theorem scan_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) (depth : ℕ) : Bounded (scanAt limits bids addresses depth).1.2 := by
  induction addresses generalizing depth with
  | nil => exact block_bound _
  | cons address rest ih =>
      have hf := fractional_bound limits bids address (depth+2)
      have hl := ih (depth+2)
      simp only [Bounded,scanAt,nodes,payload,List.length_cons,List.length_nil] at hf hl ⊢
      omega

def scanWithEmission (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) := finish (scanAt limits bids addresses 0)

theorem scanWithEmission_compat (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithEmission limits bids addresses).1 = BinaryHeapScanMeasured.scan limits bids addresses :=
  BinaryNumericalReadbackPlan.finish_compat (scan_refines limits bids addresses 0)

theorem scanWithEmission_bound (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (scanWithEmission limits bids addresses).2 ≤ 25*(scanWithEmission limits bids addresses).1.1.2.length+5 :=
  BinaryNumericalReadbackPlan.finish_bound _ (scan_bound limits bids addresses 0)

end Blotto.BinaryInitialScanPlan
