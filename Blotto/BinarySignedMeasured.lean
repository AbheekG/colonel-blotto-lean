import Blotto.BinaryArithmeticMeasured
import Blotto.BinarySignedAllocation
import Blotto.BinaryBooleanPrimitiveLifetime
import Blotto.BinaryCompareSignedMeasured

/-! Actual signed branches carry both allocation and the established complete
width work reservations. The reached forward borrow chooses whether the
backward borrow runs; no second subtraction is evaluated to obtain that charge.
The selected difference trace consumes the storage-fused signed producer;
the earlier untraced interfaces remain checked references. All observer
arithmetic remains separate from a native runtime claim. -/

namespace Blotto.BinarySignedMeasured
open BinarySignedMagnitude BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def difference (first second : List Bool) : (Word × ℕ) × ℕ :=
  let W := max first.length second.length
  let a := BinarySignedAllocation.padWithAllocation W first
  let b := BinarySignedAllocation.padWithAllocation W second
  let forward := BinaryDivisionAllocation.borrowWithAllocation a.1 b.1 false []
  if forward.1.2 then
    let backward := BinaryDivisionAllocation.borrowWithAllocation b.1 a.1 false []
    ((⟨true,backward.1.1⟩,a.2+b.2+forward.2+backward.2+4),4*(W+1)+22*(W+1)+22*(W+1))
  else ((⟨false,forward.1.1⟩,a.2+b.2+forward.2+4),4*(W+1)+22*(W+1))

theorem difference_erases (first second : List Bool) :
    (difference first second).1 = BinarySignedAllocation.differenceWithAllocation first second := by
  simp only [difference,BinarySignedAllocation.differenceWithAllocation]
  split <;> rename_i h <;> simp only [h,ite_true,ite_false]

theorem difference_data (first second : List Bool) :
    (difference first second).1.1 = BinarySignedMagnitude.difference first second := by
  rw [difference_erases,BinarySignedAllocation.differenceWithAllocation_state]

theorem difference_work (first second : List Bool) :
    (difference first second).2 = BinarySignedMagnitude.differenceWork first second := by
  simp only [difference,BinarySignedMagnitude.differenceWork,BinarySignedAllocation.padWithAllocation,
    BinaryDivisionAllocation.borrowWithAllocation_refines,BinaryBorrowWord.subtract]
  split <;> rename_i h <;> simp only [h,Bool.false_eq_true,ite_true,ite_false,Nat.add_zero]

def add (first second : Word) : (Word × ℕ) × ℕ :=
  if first.negative = second.negative then
    let added := BinaryArithmeticMeasured.add first.bits second.bits
    ((⟨first.negative,added.1.1⟩,added.1.2+3),3+added.2)
  else if first.negative then
    let result := difference second.bits first.bits
    ((result.1.1,result.1.2+3),3+result.2)
  else
    let result := difference first.bits second.bits
    ((result.1.1,result.1.2+3),3+result.2)

theorem add_erases (first second : Word) :
    (add first second).1 = BinarySignedAllocation.addWithAllocation first second := by
  simp only [add,BinarySignedAllocation.addWithAllocation,BinaryArithmeticMeasured.add_erases,difference_erases]
  split
  · rfl
  · split <;> rfl

theorem add_data (first second : Word) :
    (add first second).1.1 = BinarySignedMagnitude.add first second := by
  rw [add_erases,BinarySignedAllocation.addWithAllocation_state]

theorem add_work (first second : Word) :
    (add first second).2 = BinarySignedMagnitude.addWork first second := by
  simp only [add,BinarySignedMagnitude.addWork,BinaryArithmeticMeasured.add_work,difference_work]
  by_cases hSign : first.negative = second.negative
  · simp only [hSign,ite_true]
  · simp only [hSign,ite_false]
    cases hFirst : first.negative <;> simp only [hFirst,Bool.false_eq_true,ite_true,ite_false]

def subtract (first second : Word) : (Word × ℕ) × ℕ :=
  let result := add first (BinarySignedMagnitude.negate second)
  ((result.1.1,result.1.2+1),result.2)

theorem subtract_erases (first second : Word) :
    (subtract first second).1 = BinarySignedAllocation.subtractWithAllocation first second := by
  simp only [subtract,BinarySignedAllocation.subtractWithAllocation,add_erases]

theorem subtract_data (first second : Word) :
    (subtract first second).1.1 = BinarySignedMagnitude.subtract first second := by
  rw [subtract_erases,BinarySignedAllocation.subtractWithAllocation_state]

theorem subtract_work (first second : Word) :
    (subtract first second).2 = BinarySignedMagnitude.addWork first (BinarySignedMagnitude.negate second) := add_work _ _

def multiply (first second : Word) : (Word × ℕ) × ℕ :=
  let result := BinaryArithmeticMeasured.multiply first.bits second.bits
  ((⟨Bool.xor first.negative second.negative,result.1.1⟩,result.1.2+2),1+result.2)

theorem multiply_erases (first second : Word) :
    (multiply first second).1 = BinarySignedAllocation.multiplyWithAllocation first second := by
  simp only [multiply,BinarySignedAllocation.multiplyWithAllocation,BinaryArithmeticMeasured.multiply_erases]

theorem multiply_data (first second : Word) :
    (multiply first second).1.1 = BinarySignedMagnitude.multiply first second := by
  rw [multiply_erases,BinarySignedAllocation.multiplyWithAllocation_state]

theorem multiply_work (first second : Word) :
    (multiply first second).2 = BinarySignedMagnitude.multiplyWork first second := by
  simp only [multiply,BinarySignedMagnitude.multiplyWork,BinaryArithmeticMeasured.multiply_work]

def differenceTraced (first second : List Bool) : (Word × Trace) × ℕ :=
  let result := BinaryCompareSignedMeasured.difference first second
  ((result.data,[.frames (2*max first.length second.length+8),.arrayAllocation 8,
    .listAllocation result.storage]),result.work)

theorem differenceTraced_erases (first second : List Bool) :
    (differenceTraced first second).1 = BinaryBooleanPrimitiveLifetime.differenceWithTrace first second := by
  simp only [differenceTraced,BinaryBooleanPrimitiveLifetime.differenceWithTrace,
    BinaryCompareSignedMeasured.difference_data,BinaryCompareSignedMeasured.difference_storage,
    BinarySignedAllocation.differenceWithAllocation_state]

theorem differenceTraced_data (first second : List Bool) :
    (differenceTraced first second).1.1 = BinarySignedMagnitude.difference first second :=
  BinaryCompareSignedMeasured.difference_data _ _

theorem differenceTraced_work (first second : List Bool) :
    (differenceTraced first second).2 = BinarySignedMagnitude.differenceWork first second :=
  BinaryCompareSignedMeasured.difference_work _ _

end Blotto.BinarySignedMeasured
