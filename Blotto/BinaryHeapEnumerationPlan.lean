import Blotto.BinaryHeapEnumerationWidthMeasured
import Blotto.BinaryTracePlanMeasured

/-! Actual enumeration retains a depth-indexed plan instead of copying the
recursive trace. The old value, trace and source work are exact projections.
Only named emitter/list/shift operations are priced here. -/
namespace Blotto.BinaryHeapEnumerationPlan
open BinaryRationalEncoding BinarySeedPreparationSpace BinaryTracePlanMeasured BinaryTraceDepth
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryHeapEnumerationMeasured
set_option autoImplicit false
set_option maxHeartbeats 3000000

def view {α : Type} (produced : (α × Plan) × ℕ) : (α × Trace) × ℕ :=
  ((produced.1.1,denote produced.1.2),produced.2)

def offset {α : Type} (depth : ℕ) (produced : (α × Trace) × ℕ) : (α × Trace) × ℕ :=
  ((produced.1.1,under depth produced.1.2),produced.2)

def enumerateAt {w : ℕ} (cap pc : FixedBinaryWord w) (_hp : pc.value ≤ cap.value) (depth : ℕ) :
    (List (Address w cap) × Plan) × ℕ :=
  let guard := lt pc cap
  if hRead : guard.1.1 = true then
    have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp ((lt_data pc cap).symm.trans hRead)
    let advanced := advance pc
    have hNext : advanced.1.1.1.value = pc.value+1 := by
      rw [advance_data,BinaryIndexWord.incrementWithWork_state]
      exact (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
    let later := enumerateAt cap advanced.1.1.1 (by omega) (depth+2)
    let plan := Plan.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 16])
      (.join (.shifted (depth+2) guard.1.2) (.join (.shifted (depth+2) advanced.1.2) later.1.2))
    ((⟨pc,hLt⟩::later.1.1,plan),guard.2+advanced.2+2*(cap.bits.length+1)+later.2+4)
  else (([],.join (.block [.frames (depth+1),.arrayAllocation 8]) (.shifted (depth+2) guard.1.2)),guard.2+1)
termination_by cap.value-pc.value
decreasing_by
  rw [advance_data,BinaryIndexWord.incrementWithWork_state]
  have hNext := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

theorem enumerateAt_refines {w : ℕ} (cap pc : FixedBinaryWord w) (hp : pc.value ≤ cap.value) (depth : ℕ) :
    view (enumerateAt cap pc hp depth) = offset depth (enumerate cap pc hp) := by
  conv_lhs => unfold enumerateAt
  conv_rhs => unfold enumerate
  dsimp only
  split
  · rename_i hRead
    have hl := enumerateAt_refines cap (advance pc).1.1.1 (by
      rw [advance_data,BinaryIndexWord.incrementWithWork_state]
      have ht := (BinaryIndexWord.lt_value pc cap).mp ((lt_data pc cap).symm.trans hRead)
      have hn := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
      omega) (depth+2)
    simp only [view,offset] at hl ⊢
    have hv := congrArg (fun out => out.1.1) hl
    have ht := congrArg (fun out => out.1.2) hl
    have hw := congrArg (fun out => out.2) hl
    dsimp only at hv ht hw
    simp only [denote,hv,ht,hw,BinaryPRGHeapTraceUsage.wrapList,BinaryPRGHeapTraceUsage.wrap,
      BinaryPRGHeapTraceUsage.combine,under_append,under_compose,List.append_nil,List.append_assoc]
    rfl
  · simp only [view,offset,denote,BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,
      under_append,under_compose,List.append_nil]
    rfl
termination_by cap.value-pc.value
decreasing_by
  rw [advance_data,BinaryIndexWord.incrementWithWork_state]
  have ht := (BinaryIndexWord.lt_value pc cap).mp ((lt_data pc cap).symm.trans (by assumption))
  have hn := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

theorem advance_length {w : ℕ} (word : FixedBinaryWord w) :
    (advance word).1.2.length ≤ 3*(w+1)+2 := by
  have h := BinaryWordCoinPrimitivesMeasured.incrementBitsAt_trace_length word.bits 0
  simp only [advance,List.length_append,List.length_cons,List.length_nil,under,List.length_map]
  rw [word.size] at h
  change 2+(BinaryWordCoinPrimitivesMeasured.incrementBitsAt word.bits 0).1.2.length ≤ _
  omega

theorem enumerateAt_budget {w : ℕ} (cap pc : FixedBinaryWord w) (hp : pc.value ≤ cap.value) (depth : ℕ) :
    payload (enumerateAt cap pc hp depth).1.2+nodes (enumerateAt cap pc hp depth).1.2 ≤
      8*((enumerateAt cap pc hp depth).2+1) := by
  conv_lhs => unfold enumerateAt
  conv_rhs => unfold enumerateAt
  dsimp only
  split
  · rename_i hRead
    have hl := enumerateAt_budget cap (advance pc).1.1.1 (by
      rw [advance_data,BinaryIndexWord.incrementWithWork_state]
      have ht := (BinaryIndexWord.lt_value pc cap).mp ((lt_data pc cap).symm.trans hRead)
      have hn := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
      omega) (depth+2)
    have ha := advance_length pc
    have hg : (lt pc cap).1.2.length = 3 := rfl
    simp only [payload,nodes,List.length_cons,List.length_nil,hg,cap.size]
    omega
  · have hg : (lt pc cap).1.2.length = 3 := rfl
    simp only [payload,nodes,List.length_cons,List.length_nil,hg]
    omega
termination_by cap.value-pc.value
decreasing_by
  rw [advance_data,BinaryIndexWord.incrementWithWork_state]
  have ht := (BinaryIndexWord.lt_value pc cap).mp ((lt_data pc cap).symm.trans (by assumption))
  have hn := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

def allAt {w : ℕ} (cap : FixedBinaryWord w) (depth : ℕ) : (List (Address w cap) × Plan) × ℕ :=
  let drawn := enumerateAt cap (BinaryPRGHeapAddressEnumeration.zero cap)
    (by rw [BinaryPRGHeapAddressEnumeration.zero_value]; omega) (depth+2)
  ((drawn.1.1,.join (.block [.listAllocation cap.bits.length,.frames (depth+cap.bits.length+2),.arrayAllocation 16])
    drawn.1.2),drawn.2)

def allBitsAt (bits : List Bool) (depth : ℕ) :=
  allAt (⟨bits,rfl⟩ : FixedBinaryWord bits.length) depth

def allFromBitsAt {w : ℕ} (cap : FixedBinaryWord w) (depth : ℕ) : (List (Address w cap) × Plan) × ℕ := by
  rcases cap with ⟨bits,size⟩
  subst w
  exact allBitsAt bits depth

theorem allFromBitsAt_eq {w : ℕ} (cap : FixedBinaryWord w) (depth : ℕ) :
    allFromBitsAt cap depth = allAt cap depth := by
  cases cap with
  | mk bits size => subst w; rfl

theorem allFromBitsAt_refines {w : ℕ} (cap : FixedBinaryWord w) (depth : ℕ) :
    view (allFromBitsAt cap depth) = offset depth (BinaryHeapEnumerationWidthMeasured.allFromBits cap) := by
  rw [allFromBitsAt_eq,BinaryHeapEnumerationWidthMeasured.allFromBits_eq]
  have h := enumerateAt_refines cap (BinaryPRGHeapAddressEnumeration.zero cap)
    (by rw [BinaryPRGHeapAddressEnumeration.zero_value]; omega) (depth+2)
  simp only [view,offset] at h ⊢
  have hv := congrArg (fun out => out.1.1) h
  have ht := congrArg (fun out => out.1.2) h
  have hw := congrArg (fun out => out.2) h
  dsimp only at hv ht hw
  simp only [allAt,all,denote,hv,ht,hw,BinaryPRGHeapTraceUsage.wrapList,BinaryPRGHeapTraceUsage.wrap,
    BinaryPRGHeapTraceUsage.combine,under_append,under_compose,List.append_nil,cap.size]
  rfl

theorem allFromBitsAt_budget {w : ℕ} (cap : FixedBinaryWord w) (depth : ℕ) :
    payload (allFromBitsAt cap depth).1.2+nodes (allFromBitsAt cap depth).1.2 ≤
      16*((allFromBitsAt cap depth).2+1) := by
  rw [allFromBitsAt_eq]
  have h := enumerateAt_budget cap (BinaryPRGHeapAddressEnumeration.zero cap)
    (by rw [BinaryPRGHeapAddressEnumeration.zero_value]; omega) (depth+2)
  simp only [allAt,payload,nodes,List.length_cons,List.length_nil]
  omega

end Blotto.BinaryHeapEnumerationPlan
