import Blotto.BinaryReferenceReadMeasured
import Blotto.BinaryWordObjectArrayAccess

/-! The physical array lookup consumes the returned slot pointer in the actual
heap reader. The word, retained trace and source work are joined in one call;
semantic row witnesses remain erased and invalid indices retain EOF behavior. -/

namespace Blotto.BinaryWordObjectArrayAccessMeasured
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinaryWordObjectArray
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def get {n : ℕ} (store : Store n) (index : List Bool) : (Option SignedWord × Trace) × ℕ :=
  let slot := BinaryReferenceReadMeasured.read store.slots index
  match slot.1.1 with
  | none => ((none,wrap 16 2 [slot.1.2]),slot.2+4)
  | some pointer =>
      let object := BinaryHeapReadMeasured.read store.heap.tape pointer
      ((match object.1.1 with | some (.leaf word) => some word | _ => none,
        wrap 48 2 [slot.1.2,object.1.2]),slot.2+object.2.work+4)

theorem get_erases {n : ℕ} (store : Store n) (index : List Bool) :
    (get store index).1 = BinaryWordObjectArrayAccess.getWithTrace store index := by
  simp only [get,BinaryWordObjectArrayAccess.getWithTrace,BinaryReferenceReadMeasured.read_erases,
    BinaryHeapReadMeasured.read_erases]
  split <;> rename_i hSlot <;> simp only [hSlot] <;> rfl

theorem get_data {n : ℕ} (store : Store n) (index : List Bool) :
    (get store index).1.1 = (getWithWork store index).1 := by
  have h := congrArg Prod.fst (get_erases store index)
  exact h.trans (BinaryWordObjectArrayAccess.get_state store index)

theorem get_work {n : ℕ} (store : Store n) (index : List Bool) :
    (get store index).2 = (getWithWork store index).2 := by
  simp only [get,getWithWork,BinaryReferenceReadMeasured.read_data,BinaryReferenceReadMeasured.read_work,
    BinaryHeapReadMeasured.read_charge]
  split <;> rename_i hSlot <;> simp only [hSlot]

theorem get_realizes {n : ℕ} (store : Store n) (items : List SignedWord)
    (hStore : store.Realizes items) (index : List Bool) :
    (get store index).1.1 = items[BinaryBigEndian.littleValue index]? := by
  rw [get_erases]
  exact BinaryWordObjectArrayAccess.get_realizes store items hStore index

theorem get_bound {n : ℕ} (store : Store n) (index : List Bool) :
    (get store index).2 ≤ BinaryWordObjectArray.readBound store index.length := by
  rw [get_work]
  exact getWithWork_bound store index

theorem get_all_prefix {n : ℕ} (store : Store n) (index : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (get store index).1.2 steps ≤
        borrowed+BinaryWordObjectArrayAccess.envelope store index.length ∧
      framePeak ((get store index).1.2.take steps) ≤ BinaryWordObjectArrayAccess.envelope store index.length := by
  rw [get_erases]
  exact BinaryWordObjectArrayAccess.all_prefix store index borrowed steps

end Blotto.BinaryWordObjectArrayAccessMeasured
