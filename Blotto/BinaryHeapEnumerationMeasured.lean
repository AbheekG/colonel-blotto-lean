import Blotto.BinaryPRGHeapEnumerationLifetime
import Blotto.BinaryWordCoinPrimitivesMeasured
import Blotto.BinaryBorrowSummaryMeasured

/-! Boolean borrow guards return their actual result and storage summary in
one cached-width scan. Carry advances use direct depth-indexed traces and
cached widths. Reached enumeration preserves the old address list, trace and
work charge. Native scalar/reference/allocator realisation remains open. -/
namespace Blotto.BinaryHeapEnumerationMeasured
open BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def borrow : List Bool → List Bool → Bool → Bool × ℕ
  | a::as,b::bs,carry =>
      let later := borrow as bs (BinaryBorrowWord.nextBorrow a b carry)
      (later.1,later.2+10)
  | _,_,carry => (carry,10)

theorem borrow_data (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (borrow a b carry).1 = (BinaryBorrowWord.loop a b carry acc).2 := by
  induction a generalizing b carry acc with
  | nil => cases b <;> rfl
  | cons bit rest ih => cases b with
    | nil => rfl
    | cons other tail =>
        exact ih tail (BinaryBorrowWord.nextBorrow bit other carry) (BinaryBorrowWord.difference bit other carry::acc)

theorem borrow_work (a b : List Bool) (carry : Bool) :
    (borrow a b carry).2 = 10*BinaryBorrowWord.visits a b := by
  induction a generalizing b carry with
  | nil => cases b <;> rfl
  | cons bit rest ih => cases b with
    | nil => rfl
    | cons other tail => simp only [borrow,BinaryBorrowWord.visits,ih]; omega


def lt {w : ℕ} (first second : FixedBinaryWord w) : (Bool × Trace) × ℕ :=
  let result := BinaryBorrowSummaryMeasured.run first.bits second.bits false w 0
  ((result.answer,[.frames (2*w+4),.arrayAllocation 8,
    .listAllocation (result.held+result.allocated)]),result.work+2*w)

theorem lt_erases {w : ℕ} (first second : FixedBinaryWord w) :
    (lt first second).1 = BinaryWordStoreLifetime.ltWithTrace first second := by
  simp only [lt,BinaryBorrowSummaryMeasured.run_data,BinaryBorrowSummaryMeasured.run_storage first.bits second.bits w first.size second.size,
    BinaryWordStoreLifetime.ltWithTrace,BinaryDivisionAllocation.borrowWithAllocation_refines]

theorem lt_data {w : ℕ} (first second : FixedBinaryWord w) : (lt first second).1.1 = BinaryIndexWord.lt first second := by
  rw [lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases]

theorem lt_work {w : ℕ} (first second : FixedBinaryWord w) :
    (lt first second).2 = (BinaryIndexWord.ltWithWork first second).2 := by
  simp only [lt,BinaryBorrowSummaryMeasured.run_work,borrow_work,BinaryIndexWord.ltWithWork,first.size]

theorem incrementBits_work (bits : List Bool) :
    (BinaryWordCoinPrimitivesMeasured.incrementBits bits).2 = 4*BinaryIndexWord.incrementVisits bits := by
  exact BinaryWordCoinPrimitivesMeasured.incrementBitsAt_work bits 0

def advance {w : ℕ} (word : FixedBinaryWord w) : ((FixedBinaryWord w × Bool) × Trace) × ℕ :=
  let next := BinaryWordCoinPrimitivesMeasured.incrementBits word.bits
  have hSize : next.1.1.1.length = w := by
    rw [BinaryWordCoinPrimitivesMeasured.incrementBits_erases,BinaryWordStoreLifetime.incrementBitsWithTrace_erases,
      BinaryIndexWord.incrementBits_length,word.size]
  (((⟨next.1.1.1,hSize⟩,next.1.1.2),[.frames 2,.arrayAllocation 8]++under 2 next.1.2),next.2+2*w+2)

theorem advance_erases {w : ℕ} (word : FixedBinaryWord w) :
    (advance word).1 = BinaryWordStoreLifetime.incrementWithTrace word := by
  simp only [advance,BinaryWordStoreLifetime.incrementWithTrace,BinaryWordCoinPrimitivesMeasured.incrementBits_erases]

theorem advance_data {w : ℕ} (word : FixedBinaryWord w) :
    (advance word).1.1 = (BinaryIndexWord.incrementWithWork word).1 := by
  rw [advance_erases,BinaryWordStoreLifetime.incrementWithTrace_erases,BinaryIndexWord.incrementWithWork_state]

theorem advance_work {w : ℕ} (word : FixedBinaryWord w) :
    (advance word).2 = (BinaryIndexWord.incrementWithWork word).2 := by
  simp only [advance,incrementBits_work,BinaryIndexWord.incrementWithWork,word.size]

def enumerate {w : ℕ} (cap pc : FixedBinaryWord w) (_hp : pc.value ≤ cap.value) :
    (List (Address w cap) × Trace) × ℕ :=
  let guard := lt pc cap
  if hRead : guard.1.1 = true then
    have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp ((lt_data pc cap).symm.trans hRead)
    let advanced := advance pc
    have hNext : advanced.1.1.1.value = pc.value+1 := by
      rw [advance_data,BinaryIndexWord.incrementWithWork_state]
      exact (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
    let later := enumerate cap advanced.1.1.1 (by omega)
    ((⟨pc,hLt⟩::later.1.1,wrapList 1 16 2 [guard.1.2,advanced.1.2,later.1.2]),
      guard.2+advanced.2+2*(cap.bits.length+1)+later.2+4)
  else (([],wrap 8 1 [guard.1.2]),guard.2+1)
termination_by cap.value-pc.value
decreasing_by
  rw [advance_data,BinaryIndexWord.incrementWithWork_state]
  have hNext := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

theorem enumerate_erases {w : ℕ} (cap pc : FixedBinaryWord w) (hp : pc.value ≤ cap.value) :
    (enumerate cap pc hp).1 = BinaryPRGHeapEnumerationLifetime.enumerateWithTrace cap pc hp := by
  conv_lhs => unfold enumerate
  conv_rhs => unfold BinaryPRGHeapEnumerationLifetime.enumerateWithTrace
  dsimp only
  simp only [lt_erases]
  split
  · rename_i hRead
    have hLt := (BinaryIndexWord.lt_value pc cap).mp
      ((BinaryWordStoreLifetime.ltWithTrace_erases pc cap).symm.trans hRead)
    simp only [advance_erases]
    exact congrArg (fun later => (⟨pc,(BinaryIndexWord.lt_value pc cap).mp
      ((BinaryWordStoreLifetime.ltWithTrace_erases pc cap).symm.trans hRead)⟩::later.1,
      wrapList 1 16 2 [(BinaryWordStoreLifetime.ltWithTrace pc cap).2,
        (BinaryWordStoreLifetime.incrementWithTrace pc).2,later.2]))
      (enumerate_erases cap (BinaryWordStoreLifetime.incrementWithTrace pc).1.1 (by
        rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
        have hn := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
        have hl := (BinaryIndexWord.lt_value pc cap).mp
          ((BinaryWordStoreLifetime.ltWithTrace_erases pc cap).symm.trans hRead)
        omega))
  · rfl
termination_by cap.value-pc.value
decreasing_by
  rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
  have hl := (BinaryIndexWord.lt_value pc cap).mp
    ((BinaryWordStoreLifetime.ltWithTrace_erases pc cap).symm.trans (by assumption))
  have hn := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

theorem enumerate_work {w : ℕ} (cap pc : FixedBinaryWord w) (hp : pc.value ≤ cap.value) :
    (enumerate cap pc hp).2 = (BinaryPRGHeapAddressEnumeration.enumerateWithWork cap pc hp).2 := by
  conv_lhs => unfold enumerate
  conv_rhs => unfold BinaryPRGHeapAddressEnumeration.enumerateWithWork
  dsimp only
  by_cases hRead : (lt pc cap).1.1 = true
  · have hOld : (BinaryIndexWord.ltWithWork pc cap).1 = true :=
      (BinaryIndexWord.ltWithWork_state pc cap).trans ((lt_data pc cap).symm.trans hRead)
    rw [dite_eq_left hRead,dite_eq_left hOld]
    dsimp only
    simp only [advance_data,advance_work]
    rw [lt_work]
    rw [enumerate_work]
  · have hOld : ¬ (BinaryIndexWord.ltWithWork pc cap).1 = true := fun h =>
      hRead ((lt_data pc cap).trans ((BinaryIndexWord.ltWithWork_state pc cap).symm.trans h))
    rw [dite_eq_right hRead,dite_eq_right hOld]
    simp only [lt_work]
termination_by cap.value-pc.value
decreasing_by
  rw [BinaryIndexWord.incrementWithWork_state]
  have hl := (BinaryIndexWord.lt_value pc cap).mp ((lt_data pc cap).symm.trans (by assumption))
  have hn := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

def all {w : ℕ} (cap : FixedBinaryWord w) : (List (Address w cap) × Trace) × ℕ :=
  let drawn := enumerate cap (BinaryPRGHeapAddressEnumeration.zero cap)
    (by rw [BinaryPRGHeapAddressEnumeration.zero_value]; omega)
  ((drawn.1.1,wrapList w 16 (w+2) [drawn.1.2]),drawn.2)

theorem all_erases {w : ℕ} (cap : FixedBinaryWord w) :
    (all cap).1 = BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace cap := by
  rw [BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace_eq]
  simp only [all,BinaryPRGHeapEnumerationLifetime.allWithTrace,enumerate_erases]

theorem all_work {w : ℕ} (cap : FixedBinaryWord w) :
    (all cap).2 = (BinaryPRGHeapAddressEnumeration.allWithWork cap).2 :=
  enumerate_work cap (BinaryPRGHeapAddressEnumeration.zero cap) _

end Blotto.BinaryHeapEnumerationMeasured
