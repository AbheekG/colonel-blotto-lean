import Blotto.BinaryHeapEnumerationWidthMeasured
import Blotto.BinaryNumericalReadbackPlan

/-! Reached borrow guards, Boolean increments and address conses collect one
final-depth enumeration plan. A measured structural zero map supplies the actual
initial word. One final emission retains the complete old record and returns
zero-map plus emission work separately. Native metadata/reference costs remain. -/
namespace Blotto.BinaryAddressEnumerationPlan
open BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth BinaryTracePlanMeasured
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines finish)
open BinaryCachePrefixPlan (Bounded block_bound)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def zeroBits : List Bool → List Bool × ℕ
  | [] => ([],2)
  | _::rest => let later := zeroBits rest; (false::later.1,later.2+4)

theorem zeroBits_data (bits : List Bool) : (zeroBits bits).1 = bits.map (fun _ => false) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [zeroBits,List.map_cons,ih]

theorem zeroBits_work (bits : List Bool) : (zeroBits bits).2 = 4*bits.length+2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [zeroBits,List.length_cons,ih]; omega

def zeroWord {w : ℕ} (cap : FixedBinaryWord w) : FixedBinaryWord w × ℕ :=
  let produced := zeroBits cap.bits
  (⟨produced.1,by simp only [produced,zeroBits_data,List.length_map,cap.size]⟩,produced.2)

theorem zeroWord_data {w : ℕ} (cap : FixedBinaryWord w) :
    (zeroWord cap).1 = BinaryPRGHeapAddressEnumeration.zero cap := by
  simp only [zeroWord,zeroBits_data,BinaryPRGHeapAddressEnumeration.zero]

theorem zeroWord_work {w : ℕ} (cap : FixedBinaryWord w) : (zeroWord cap).2 = 4*w+2 := by
  simp only [zeroWord,zeroBits_work,cap.size]

def guardAt {w : ℕ} (pc cap : FixedBinaryWord w) (depth : ℕ) : (Bool × Plan) × ℕ :=
  let result := BinaryBorrowSummaryMeasured.run pc.bits cap.bits false w 0
  ((result.answer,.block [.frames (depth+(2*w+4)),.arrayAllocation 8,
    .listAllocation (result.held+result.allocated)]),result.work+2*w)

theorem guard_refines {w : ℕ} (pc cap : FixedBinaryWord w) (depth : ℕ) :
    view (guardAt pc cap depth) = offset depth (BinaryHeapEnumerationMeasured.lt pc cap) := rfl

theorem guard_data {w : ℕ} (pc cap : FixedBinaryWord w) (depth : ℕ) :
    (guardAt pc cap depth).1.1 = (BinaryHeapEnumerationMeasured.lt pc cap).1.1 := data_refines (guard_refines pc cap depth)

theorem guard_trace {w : ℕ} (pc cap : FixedBinaryWord w) (depth : ℕ) :
    denote (guardAt pc cap depth).1.2 = under depth (BinaryHeapEnumerationMeasured.lt pc cap).1.2 := trace_refines (guard_refines pc cap depth)

theorem guard_work {w : ℕ} (pc cap : FixedBinaryWord w) (depth : ℕ) :
    (guardAt pc cap depth).2 = (BinaryHeapEnumerationMeasured.lt pc cap).2 := charge_refines (guard_refines pc cap depth)

def advanceAt {w : ℕ} (pc : FixedBinaryWord w) (depth : ℕ) : ((FixedBinaryWord w × Bool) × Plan) × ℕ :=
  let next := BinaryWordCoinPrimitivesMeasured.incrementBitsAt pc.bits (depth+2)
  have hSize : next.1.1.1.length = w := by
    rw [BinaryWordCoinPrimitivesMeasured.incrementBitsAt_erases,BinaryWordStoreLifetime.incrementBitsWithTrace_erases,
      BinaryIndexWord.incrementBits_length,pc.size]
  (((⟨next.1.1.1,hSize⟩,next.1.1.2),.join (.block [.frames (depth+2),.arrayAllocation 8]) (.block next.1.2)),next.2+2*w+2)

theorem advance_refines {w : ℕ} (pc : FixedBinaryWord w) (depth : ℕ) :
    view (advanceAt pc depth) = offset depth (BinaryHeapEnumerationMeasured.advance pc) := by
  simp only [advanceAt,BinaryHeapEnumerationMeasured.advance,view,offset,denote,
    BinaryWordCoinPrimitivesMeasured.incrementBitsAt_erases,BinaryWordCoinPrimitivesMeasured.incrementBits_erases,
    BinaryWordCoinPrimitivesMeasured.incrementBitsAt_work,BinaryHeapEnumerationMeasured.incrementBits_work,
    under_append,under_compose]
  rfl

theorem advance_data {w : ℕ} (pc : FixedBinaryWord w) (depth : ℕ) :
    (advanceAt pc depth).1.1 = (BinaryHeapEnumerationMeasured.advance pc).1.1 := data_refines (advance_refines pc depth)

theorem advance_trace {w : ℕ} (pc : FixedBinaryWord w) (depth : ℕ) :
    denote (advanceAt pc depth).1.2 = under depth (BinaryHeapEnumerationMeasured.advance pc).1.2 := trace_refines (advance_refines pc depth)

theorem advance_work {w : ℕ} (pc : FixedBinaryWord w) (depth : ℕ) :
    (advanceAt pc depth).2 = (BinaryHeapEnumerationMeasured.advance pc).2 := charge_refines (advance_refines pc depth)

theorem advance_value {w : ℕ} (cap pc : FixedBinaryWord w) (hLt : pc.value < cap.value) (depth : ℕ) :
    (advanceAt pc depth).1.1.1.value = pc.value+1 := by
  rw [advance_data,BinaryHeapEnumerationMeasured.advance_data,BinaryIndexWord.incrementWithWork_state]
  exact (BinaryIndexWord.increment_value pc (by have hc := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1

def enumerateAt {w : ℕ} (cap pc : FixedBinaryWord w) (_hp : pc.value ≤ cap.value) (depth : ℕ) :
    (List (Address w cap) × Plan) × ℕ :=
  let guard := guardAt pc cap (depth+2)
  if hRead : guard.1.1 = true then
    have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp
      ((BinaryHeapEnumerationMeasured.lt_data pc cap).symm.trans ((guard_data pc cap (depth+2)).symm.trans hRead))
    let advanced := advanceAt pc (depth+2)
    have hNext : advanced.1.1.1.value = pc.value+1 := advance_value cap pc hLt (depth+2)
    let later := enumerateAt cap advanced.1.1.1 (by omega) (depth+2)
    ((⟨pc,hLt⟩::later.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 16])
      (.join guard.1.2 (.join advanced.1.2 later.1.2))),
      guard.2+advanced.2+2*(cap.bits.length+1)+later.2+4)
  else (([],.join (.block [.frames (depth+1),.arrayAllocation 8]) guard.1.2),guard.2+1)
termination_by cap.value-pc.value
decreasing_by
  have hRead : (guardAt pc cap (depth+2)).1.1 = true := by assumption
  have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp
    ((BinaryHeapEnumerationMeasured.lt_data pc cap).symm.trans ((guard_data pc cap (depth+2)).symm.trans hRead))
  rw [advance_value cap pc hLt]
  omega

theorem enumerate_refines {w : ℕ} (cap pc : FixedBinaryWord w) (hp : pc.value ≤ cap.value) (depth : ℕ) :
    view (enumerateAt cap pc hp depth) = offset depth (BinaryHeapEnumerationMeasured.enumerate cap pc hp) := by
  conv_lhs => unfold enumerateAt
  conv_rhs => unfold BinaryHeapEnumerationMeasured.enumerate
  dsimp only
  simp only [guard_data]
  split
  · rename_i hRead
    have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp ((BinaryHeapEnumerationMeasured.lt_data pc cap).symm.trans hRead)
    have hNext : (BinaryHeapEnumerationMeasured.advance pc).1.1.1.value = pc.value+1 := by
      rw [BinaryHeapEnumerationMeasured.advance_data,BinaryIndexWord.incrementWithWork_state]
      exact (BinaryIndexWord.increment_value pc (by have hc := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
    have hl := enumerate_refines cap (BinaryHeapEnumerationMeasured.advance pc).1.1.1 (by omega) (depth+2)
    simp only [view,offset,denote,guard_trace,guard_work,advance_data,advance_trace,advance_work,
      data_refines hl,trace_refines hl,charge_refines hl,wrapList,wrap,combine,List.append_nil,under_append,under_compose]
    rfl
  · simp only [view,offset,denote,guard_trace,guard_work,wrap,combine,List.append_nil,under_append,under_compose]
    rfl
termination_by cap.value-pc.value
decreasing_by
  rw [BinaryHeapEnumerationMeasured.advance_data,BinaryIndexWord.incrementWithWork_state]
  have hRead : (BinaryHeapEnumerationMeasured.lt pc cap).1.1 = true := by assumption
  have hLt := (BinaryIndexWord.lt_value pc cap).mp ((BinaryHeapEnumerationMeasured.lt_data pc cap).symm.trans hRead)
  have hn := (BinaryIndexWord.increment_value pc (by have hc := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

theorem enumerate_bound {w : ℕ} (cap pc : FixedBinaryWord w) (hp : pc.value ≤ cap.value) (depth : ℕ) :
    Bounded (enumerateAt cap pc hp depth).1.2 := by
  unfold enumerateAt
  dsimp only
  split
  · rename_i hRead
    have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp
      ((BinaryHeapEnumerationMeasured.lt_data pc cap).symm.trans ((guard_data pc cap (depth+2)).symm.trans hRead))
    have hl := enumerate_bound cap (advanceAt pc (depth+2)).1.1.1 (by rw [advance_value cap pc hLt]; omega) (depth+2)
    simp only [Bounded,guardAt,advanceAt,nodes,payload,List.length_cons,List.length_nil] at hl ⊢
    omega
  · simp [Bounded,guardAt,nodes,payload]
termination_by cap.value-pc.value
decreasing_by
  have hRead : (guardAt pc cap (depth+2)).1.1 = true := by assumption
  have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp
    ((BinaryHeapEnumerationMeasured.lt_data pc cap).symm.trans ((guard_data pc cap (depth+2)).symm.trans hRead))
  rw [advance_value cap pc hLt]
  omega

def allAt {w : ℕ} (cap : FixedBinaryWord w) (depth : ℕ) :=
  let zeroed := zeroWord cap
  let drawn := enumerateAt cap zeroed.1 (by rw [zeroWord_data,BinaryPRGHeapAddressEnumeration.zero_value]; omega) (depth+2)
  (((drawn.1.1,Plan.join (.block [.listAllocation w,.frames (depth+(w+2)),.arrayAllocation 16]) drawn.1.2),drawn.2),zeroed.2)

theorem all_refines {w : ℕ} (cap : FixedBinaryWord w) (depth : ℕ) :
    view (allAt cap depth).1 = offset depth (BinaryHeapEnumerationMeasured.all cap) := by
  have h := enumerate_refines cap (BinaryPRGHeapAddressEnumeration.zero cap) (by rw [BinaryPRGHeapAddressEnumeration.zero_value]; omega) (depth+2)
  simp only [allAt,BinaryHeapEnumerationMeasured.all,zeroWord_data,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,wrapList,wrap,combine,List.append_nil,under_append,under_compose]
  rfl

theorem all_bound {w : ℕ} (cap : FixedBinaryWord w) (depth : ℕ) : Bounded (allAt cap depth).1.1.2 := by
  have h := enumerate_bound cap (zeroWord cap).1 (by rw [zeroWord_data,BinaryPRGHeapAddressEnumeration.zero_value]; omega) (depth+2)
  simp only [Bounded,allAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def allWithEmission {w : ℕ} (cap : FixedBinaryWord w) :=
  let planned := allAt cap 0
  let emitted := finish planned.1
  (emitted.1,planned.2+emitted.2)

theorem allWithEmission_compat {w : ℕ} (cap : FixedBinaryWord w) :
    (allWithEmission cap).1 = BinaryHeapEnumerationMeasured.all cap :=
  BinaryNumericalReadbackPlan.finish_compat (all_refines cap 0)

theorem allWithEmission_extra {w : ℕ} (cap : FixedBinaryWord w) :
    (allWithEmission cap).2 ≤ 4*w+25*(allWithEmission cap).1.1.2.length+7 := by
  have h := BinaryNumericalReadbackPlan.finish_bound (allAt cap 0).1 (all_bound cap 0)
  simp only [allWithEmission,allAt,zeroWord_work] at h ⊢
  omega

theorem allWithEmission_total {w : ℕ} (cap : FixedBinaryWord w) :
    (allWithEmission cap).1.2+(allWithEmission cap).2 ≤
      cap.value*(20*(w+1)+4)+16*w+25*(allWithEmission cap).1.1.2.length+20 := by
  have he := allWithEmission_extra cap
  have hw := BinaryPRGHeapAddressEnumeration.allWithWork_bound cap
  rw [← BinaryHeapEnumerationMeasured.all_work,← allWithEmission_compat] at hw
  omega

def allBits (bits : List Bool) := allWithEmission (⟨bits,rfl⟩ : FixedBinaryWord bits.length)

def allFromBits {w : ℕ} (cap : FixedBinaryWord w) :
    ((List (Address w cap) × Trace) × ℕ) × ℕ := by
  rcases cap with ⟨bits,size⟩
  subst w
  exact allBits bits

theorem allFromBits_compat {w : ℕ} (cap : FixedBinaryWord w) :
    (allFromBits cap).1 = BinaryHeapEnumerationWidthMeasured.allFromBits cap := by
  cases cap with
  | mk bits size => subst w; exact allWithEmission_compat _

theorem allFromBits_total {w : ℕ} (cap : FixedBinaryWord w) :
    (allFromBits cap).1.2+(allFromBits cap).2 ≤
      cap.value*(20*(w+1)+4)+16*w+25*(allFromBits cap).1.1.2.length+20 := by
  cases cap with
  | mk bits size => subst w; exact allWithEmission_total _

end Blotto.BinaryAddressEnumerationPlan
