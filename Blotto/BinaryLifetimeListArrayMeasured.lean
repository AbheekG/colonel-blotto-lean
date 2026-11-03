import Blotto.BinaryLifetimeListArray
import Blotto.BinaryLifetimeArrayMeasured

/-! A measured pinned list-to-array push loop shares its actual pushed array
with the preceding trace. A complete old-array reference-copy allowance is
charged on each push. Native reference-bit, capacity/ownership, observer and
allocator realization remain separate. -/

namespace Blotto.BinaryLifetimeListArrayMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2500000

def push {α : Type*} (capacity : ℕ) : List α → Array α → (Array α × Trace) × ℕ
  | [],acc => ((acc,[.frames 1]),4)
  | item::rest,acc =>
      let later := push capacity rest (acc.push item)
      ((later.1.1,[.frames 1,.arrayAllocation capacity]++under 1 later.1.2),acc.size+later.2+9)

theorem push_erases {α : Type*} (capacity : ℕ) (items : List α) (acc : Array α) :
    (push capacity items acc).1 = BinaryLifetimeListArray.pushWithTrace capacity items acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => simp only [push,BinaryLifetimeListArray.pushWithTrace,ih]

theorem push_work {α : Type*} (capacity : ℕ) (items : List α) (acc : Array α) :
    (push capacity items acc).2 = (BinaryLifetimeArrayMeasured.pack items acc).2 := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => simp only [push,BinaryLifetimeArrayMeasured.pack,ih]

theorem push_bound {α : Type*} (capacity : ℕ) (items : List α) (acc : Array α) (B : ℕ)
    (h : acc.size+items.length ≤ B) : (push capacity items acc).2 ≤ items.length*(B+9)+4 := by
  rw [push_work]
  exact BinaryLifetimeArrayMeasured.pack_bound items acc B h

def toArray {α : Type*} (items : List α) : (Array α × Trace) × ℕ :=
  let built := push items.length items (Array.mkEmpty items.length)
  ((built.1.1,[.arrayAllocation items.length,.frames (items.length+1)]++built.1.2),built.2+2*items.length+4)

theorem toArray_erases {α : Type*} (items : List α) :
    (toArray items).1 = BinaryLifetimeListArray.toArrayWithTrace items := by
  simp only [toArray,BinaryLifetimeListArray.toArrayWithTrace,push_erases]

theorem toArray_bound {α : Type*} (items : List α) :
    (toArray items).2 ≤ items.length*(items.length+11)+8 := by
  have h := push_bound items.length items (Array.mkEmpty items.length) items.length (by simp)
  change _+2*items.length+4 ≤ _
  nlinarith only [h]

def table {α : Type*} (items : List α) : (FixedArrayTable items.length α × Trace) × ℕ :=
  let built := toArray items
  ((⟨built.1.1,(by rw [toArray_erases,BinaryLifetimeListArray.toArrayWithTrace_state]; simp)⟩,built.1.2),built.2)

theorem table_erases {α : Type*} (items : List α) :
    (table items).1 = BinaryLifetimeListArray.tableWithTrace items := by
  simp only [table,BinaryLifetimeListArray.tableWithTrace,toArray_erases]

theorem table_array {α : Type*} (items : List α) : (table items).1.1.data = items.toArray := by
  rw [table_erases,BinaryLifetimeListArray.tableWithTrace_state]

theorem table_bound {α : Type*} (items : List α) :
    (table items).2 ≤ items.length*(items.length+11)+8 := toArray_bound items

theorem all_prefix {α : Type*} (items : List α) (borrowed steps : ℕ) :
    retainedHeap borrowed (table items).1.2 steps ≤ borrowed+(items.length*(items.length+1)+items.length+1) ∧
      framePeak ((table items).1.2.take steps) ≤ items.length*(items.length+1)+items.length+1 := by
  rw [table_erases]
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ (BinaryLifetimeListArray.tableWithTrace_usage items) borrowed steps

end Blotto.BinaryLifetimeListArrayMeasured
