import Blotto.BinaryWordStoreMeasured
import Blotto.BooleanArrayIndexWork

/-! The Boolean index list, retained allocation trace and amortized work are
produced by one carry execution; numeric indices occur only in erased proofs. -/

namespace Blotto.BooleanArrayIndexMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def loop {α : Type*} : List α → List Bool → ((List (List Bool) × List Bool) × Trace) × ℕ
  | [],counter => ((([],counter),wrap 8 1 []),4)
  | _::rest,counter =>
      let advanced := BinaryWordStoreMeasured.carry counter
      let later := loop rest advanced.1.1
      (((counter::later.1.1.1,later.1.1.2),wrapList 1 16 2 [advanced.1.2,later.1.2]),
        advanced.2+later.2+8)

theorem loop_erases {α : Type*} (ruler : List α) (counter : List Bool) :
    (loop ruler counter).1 = BooleanArrayIndexEnumeration.loopWithTrace ruler counter := by
  induction ruler generalizing counter with
  | nil => rfl
  | cons item rest ih => simp only [loop,BooleanArrayIndexEnumeration.loopWithTrace,
      BinaryWordStoreMeasured.carry_erases,ih]

theorem loop_work {α : Type*} (ruler : List α) (counter : List Bool) :
    (loop ruler counter).2 = (BooleanArrayIndexWork.loopWithWork ruler counter).2 := by
  induction ruler generalizing counter with
  | nil => rfl
  | cons item rest ih => simp only [loop,BooleanArrayIndexWork.loopWithWork,
      BinaryWordStoreMeasured.carry_work,BinaryWordStoreWork.carry_work,BooleanArrayIndexWork.carry_work,
      BinaryWordStoreMeasured.carry_erases,BinaryWordStoreLifetime.carryWithTrace_erases,
      BooleanArrayIndexWork.carry_state,ih]

def enumerate {α : Type*} (ruler : List α) : (List (List Bool) × Trace) × ℕ :=
  let built := loop ruler []
  ((built.1.1.1,built.1.2),built.2)

theorem enumerate_erases {α : Type*} (ruler : List α) :
    (enumerate ruler).1 = BooleanArrayIndexEnumeration.enumerateWithTrace ruler := by
  simp only [enumerate,BooleanArrayIndexEnumeration.enumerateWithTrace,loop_erases]

theorem enumerate_work {α : Type*} (ruler : List α) :
    (enumerate ruler).2 = (BooleanArrayIndexWork.enumerateWithWork ruler).2 := by
  simp only [enumerate,BooleanArrayIndexWork.enumerateWithWork,loop_work]

theorem enumerate_bound {α : Type*} (ruler : List α) : (enumerate ruler).2 ≤ 16*ruler.length+4 := by
  rw [enumerate_work]
  exact BooleanArrayIndexWork.enumerate_work ruler

theorem enumerate_all_prefix {α : Type*} (ruler : List α) (borrowed steps : ℕ) :
    retainedHeap borrowed (enumerate ruler).1.2 steps ≤ borrowed+32*ruler.length+16 ∧
      framePeak ((enumerate ruler).1.2.take steps) ≤ 32*ruler.length+16 := by
  rw [enumerate_erases]
  exact BooleanArrayIndexEnumeration.all_prefix ruler borrowed steps

end Blotto.BooleanArrayIndexMeasured
