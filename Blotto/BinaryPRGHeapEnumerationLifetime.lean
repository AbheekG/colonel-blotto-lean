import Blotto.BinaryPRGHeapTraceUsage
import Blotto.BinaryPRGHeapAddressEnumeration
import Blotto.BinaryWordStoreLifetime

/-! Boolean cap-only address enumeration with retained comparison, increment,
identifier-list and source-frame allocations. No logical tree is constructed. -/

namespace Blotto.BinaryPRGHeapEnumerationLifetime
open BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
set_option maxHeartbeats 1500000

variable {width : ℕ}

def enumerateWithTrace (cap pc : FixedBinaryWord width) (_hp : pc.value ≤ cap.value) :
    List (Address width cap) × Trace :=
  let guard := BinaryWordStoreLifetime.ltWithTrace pc cap
  if hRead : guard.1 = true then
    have hLt : pc.value < cap.value := (BinaryIndexWord.lt_value pc cap).mp
      ((BinaryWordStoreLifetime.ltWithTrace_erases pc cap).symm.trans hRead)
    let advanced := BinaryWordStoreLifetime.incrementWithTrace pc
    have hNext : advanced.1.1.value = pc.value + 1 := by
      rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
      exact (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
    let later := enumerateWithTrace cap advanced.1.1 (by omega)
    (⟨pc,hLt⟩ :: later.1,wrapList 1 16 2 [guard.2,advanced.2,later.2])
  else ([],wrap 8 1 [guard.2])
termination_by cap.value - pc.value
decreasing_by
  rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
  have hn := (BinaryIndexWord.increment_value pc (by have h := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

theorem enumerateWithTrace_erasure (cap pc : FixedBinaryWord width) (hp : pc.value ≤ cap.value) :
    (enumerateWithTrace cap pc hp).1 = (BinaryPRGHeapAddressEnumeration.enumerateWithWork cap pc hp).1 := by
  conv_lhs => unfold enumerateWithTrace
  conv_rhs => unfold BinaryPRGHeapAddressEnumeration.enumerateWithWork
  dsimp only [BinaryIndexWord.ltWithWork]
  simp only [BinaryWordStoreLifetime.ltWithTrace_erases]
  split
  · rename_i hRead
    simp only [BinaryWordStoreLifetime.incrementWithTrace_erases,BinaryIndexWord.incrementWithWork_state]
    exact congrArg (fun rest => (⟨pc,(BinaryIndexWord.lt_value pc cap).mp hRead⟩ : Address width cap) :: rest)
      (enumerateWithTrace_erasure cap (BinaryIndexWord.increment pc).1 (by
        have hn := (BinaryIndexWord.increment_value pc (by
          have hc := BinaryPRGHeapAddressEnumeration.cap_room cap
          have hl := (BinaryIndexWord.lt_value pc cap).mp hRead
          omega)).1
        have hl := (BinaryIndexWord.lt_value pc cap).mp hRead
        omega))
  · rfl
termination_by cap.value - pc.value
decreasing_by
  have hRead : BinaryIndexWord.lt pc cap = true := by assumption
  have hl := (BinaryIndexWord.lt_value pc cap).mp hRead
  have hn := (BinaryIndexWord.increment_value pc (by have hc := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
  omega

def localEnvelope (width : ℕ) : ℕ := 6 * (width + 1)^2 + 8 * width + 64

theorem enumerateWithTrace_usage (cap pc : FixedBinaryWord width) (hp : pc.value ≤ cap.value) :
    usage (enumerateWithTrace cap pc hp).2 ≤ (cap.value - pc.value + 1) * localEnvelope width := by
  conv_lhs => unfold enumerateWithTrace
  dsimp only
  split
  · rename_i hRead
    have hl := (BinaryIndexWord.lt_value pc cap).mp
      ((BinaryWordStoreLifetime.ltWithTrace_erases pc cap).symm.trans hRead)
    have hn : (BinaryWordStoreLifetime.incrementWithTrace pc).1.1.value = pc.value + 1 := by
      rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
      exact (BinaryIndexWord.increment_value pc (by have hc := BinaryPRGHeapAddressEnumeration.cap_room cap; omega)).1
    have hLater := enumerateWithTrace_usage cap (BinaryWordStoreLifetime.incrementWithTrace pc).1.1 (by omega)
    have hGuard := BinaryWordStoreLifetime.ltWithTrace_bounds pc cap
    have hAdvance := BinaryWordStoreLifetime.incrementWithTrace_bounds pc
    have hw := wrapList_usage 1 16 2 [(BinaryWordStoreLifetime.ltWithTrace pc cap).2,
      (BinaryWordStoreLifetime.incrementWithTrace pc).2,
      (enumerateWithTrace cap (BinaryWordStoreLifetime.incrementWithTrace pc).1.1 (by omega)).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    have hRemain : cap.value - pc.value + 1 = (cap.value - (BinaryWordStoreLifetime.incrementWithTrace pc).1.1.value + 1) + 1 := by omega
    rw [hRemain,Nat.add_mul,one_mul]
    dsimp only
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells localEnvelope at *
    omega
  · have hGuard := BinaryWordStoreLifetime.ltWithTrace_bounds pc cap
    have hw := wrap_usage 8 1 [(BinaryWordStoreLifetime.ltWithTrace pc cap).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    have hm := Nat.mul_le_mul_right (localEnvelope width) (show 1 ≤ cap.value - pc.value + 1 by omega)
    dsimp only
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells localEnvelope at *
    omega
termination_by cap.value - pc.value
decreasing_by omega

def allWithTrace (cap : FixedBinaryWord width) : List (Address width cap) × Trace :=
  let drawn := enumerateWithTrace cap (BinaryPRGHeapAddressEnumeration.zero cap)
    (by rw [BinaryPRGHeapAddressEnumeration.zero_value]; omega)
  (drawn.1,wrapList width 16 (width + 2) [drawn.2])

theorem allWithTrace_erasure (cap : FixedBinaryWord width) :
    (allWithTrace cap).1 = (BinaryPRGHeapAddressEnumeration.allWithWork cap).1 := by
  simp only [allWithTrace,BinaryPRGHeapAddressEnumeration.allWithWork,enumerateWithTrace_erasure]

def envelope (count width : ℕ) : ℕ := (count + 1) * localEnvelope width + 2 * width + 20

theorem allWithTrace_usage (cap : FixedBinaryWord width) :
    usage (allWithTrace cap).2 ≤ envelope cap.value width := by
  have h := enumerateWithTrace_usage cap (BinaryPRGHeapAddressEnumeration.zero cap)
    (by rw [BinaryPRGHeapAddressEnumeration.zero_value]; omega)
  have hw := wrapList_usage width 16 (width + 2)
    [(enumerateWithTrace cap (BinaryPRGHeapAddressEnumeration.zero cap)
      (by rw [BinaryPRGHeapAddressEnumeration.zero_value]; omega)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  simp only [BinaryPRGHeapAddressEnumeration.zero_value,Nat.sub_zero] at h
  unfold allWithTrace envelope
  dsimp only
  omega

/- The numerical type index may be an expensive source expression. Recover
it from the actual bits before calling the recursive observer. The transport
and source-index equality are erased; no source tree is evaluated for width. -/
def allBitsWithTrace (bits : List Bool) :=
  allWithTrace (⟨bits,rfl⟩ : FixedBinaryWord bits.length)

def allFromBitsWithTrace (cap : FixedBinaryWord width) : List (Address width cap) × Trace := by
  rcases cap with ⟨bits,size⟩
  subst width
  exact allBitsWithTrace bits

theorem allFromBitsWithTrace_eq (cap : FixedBinaryWord width) :
    allFromBitsWithTrace cap = allWithTrace cap := by
  cases cap with
  | mk bits size =>
      subst width
      rfl

theorem allFromBitsWithTrace_erasure (cap : FixedBinaryWord width) :
    (allFromBitsWithTrace cap).1 = (BinaryPRGHeapAddressEnumeration.allWithWork cap).1 := by
  rw [allFromBitsWithTrace_eq,allWithTrace_erasure]

theorem allFromBitsWithTrace_usage (cap : FixedBinaryWord width) :
    usage (allFromBitsWithTrace cap).2 ≤ envelope cap.value width := by
  rw [allFromBitsWithTrace_eq]
  exact allWithTrace_usage cap

end Blotto.BinaryPRGHeapEnumerationLifetime
