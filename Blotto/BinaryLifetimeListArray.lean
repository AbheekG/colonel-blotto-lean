import Blotto.BinaryPRGHeapTraceUsage

/-! Generic retained list-to-array construction for parsed words. Initial and
all permitted copied array versions reserve final capacity. The input list
and referenced element payloads stay borrowed; no uniqueness is assumed. -/
namespace Blotto.BinaryLifetimeListArray
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def pushWithTrace {α : Type*} (capacity : ℕ) : List α → Array α → Array α × Trace
  | [], acc => (acc,[.frames 1])
  | item::rest, acc =>
      let later := pushWithTrace capacity rest (acc.push item)
      (later.1,[.frames 1,.arrayAllocation capacity]++under 1 later.2)

theorem pushWithTrace_state {α : Type*} (capacity : ℕ) (items : List α) (acc : Array α) :
    (pushWithTrace capacity items acc).1 = List.toArrayAux items acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => exact ih (acc.push item)

theorem pushWithTrace_bounds {α : Type*} (capacity : ℕ) (items : List α) (acc : Array α) :
    listCells (pushWithTrace capacity items acc).2 = 0 ∧
    arraySlots (pushWithTrace capacity items acc).2 = items.length*capacity ∧
    framePeak (pushWithTrace capacity items acc).2 ≤ items.length+1 := by
  induction items generalizing acc with
  | nil => simp [pushWithTrace,listCells,arraySlots,framePeak]
  | cons item rest ih =>
      have ht := ih (acc.push item)
      have hu := framePeak_under 1 (pushWithTrace capacity rest (acc.push item)).2
      simp only [pushWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,
        framePeak,listCells_under,arraySlots_under,List.length_cons]
      exact ⟨by omega,by nlinarith,by omega⟩

def toArrayWithTrace {α : Type*} (items : List α) : Array α × Trace :=
  let built := pushWithTrace items.length items (Array.mkEmpty items.length)
  (built.1,[.arrayAllocation items.length,.frames (items.length+1)]++built.2)

theorem toArrayWithTrace_state {α : Type*} (items : List α) : (toArrayWithTrace items).1 = items.toArray := by
  apply Array.toList_inj.mp
  simp [toArrayWithTrace,pushWithTrace_state,Array.toArrayAux_eq,Array.mkEmpty]

theorem toArray_prefix_capacity {α : Type*} (items : List α) (steps : ℕ) :
    (List.toArrayAux (items.take steps) (Array.mkEmpty items.length)).size ≤ items.length := by
  have ht : (items.take steps).length ≤ items.length := by simp
  have hs : (List.toArrayAux (items.take steps) (Array.mkEmpty items.length)).size = (items.take steps).length := by
    rw [← Array.length_toList,Array.toArrayAux_eq,List.length_append,Array.length_toList]
    simp
  omega

theorem toArrayWithTrace_usage {α : Type*} (items : List α) :
    usage (toArrayWithTrace items).2 ≤ items.length*(items.length+1)+items.length+1 := by
  have h := pushWithTrace_bounds items.length items (Array.mkEmpty items.length)
  unfold toArrayWithTrace usage BinaryPRGHeapPrimitiveLifetime.cells
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,Nat.max_zero]
  rw [h.1,h.2.1,max_eq_left h.2.2]
  nlinarith

def tableWithTrace {α : Type*} (items : List α) : FixedArrayTable items.length α × Trace :=
  let built := toArrayWithTrace items
  (⟨built.1,by rw [toArrayWithTrace_state]; simp⟩,built.2)

theorem tableWithTrace_state {α : Type*} (items : List α) :
    (tableWithTrace items).1 = (⟨items.toArray,by simp⟩ : FixedArrayTable items.length α) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  change (toArrayWithTrace items).1[j.val]'_ = items.toArray[j.val]'_
  congr 1
  exact toArrayWithTrace_state items

theorem tableWithTrace_usage {α : Type*} (items : List α) :
    usage (tableWithTrace items).2 ≤ items.length*(items.length+1)+items.length+1 :=
  toArrayWithTrace_usage items

end Blotto.BinaryLifetimeListArray
