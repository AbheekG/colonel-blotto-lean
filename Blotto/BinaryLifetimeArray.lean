import Blotto.BinarySeedPreparationSpace
import Blotto.NativeArrayConversionCore
import Blotto.BinaryLifetimeFlattenList

/-! Array construction reservations used by the source lifetime interpreters.
The selected builder enumerates produced entry/trace pairs once and reuses
them for the table and concatenated trace. `buildReference` retains the former
two-enumeration definition for an exact extensional refinement proof. A full
reference region is reserved for every old/new array prefix. Stored entry
payloads remain covered by the entry producer, so this counts references and
source records separately. No exclusive-ownership or reclamation premise. -/
set_option autoImplicit false
namespace Blotto.BinaryLifetimeArray
open BinarySeedPreparationSpace
open scoped BigOperators

def children (n : ℕ) (traces : Fin n → Trace) : Trace := (List.ofFn traces).flatten

theorem children_listCells (n : ℕ) (traces : Fin n → Trace) :
    listCells (children n traces)=∑ j,listCells (traces j) := by
  induction n with
  | zero => simp [children,listCells]
  | succ n ih =>
      unfold children
      rw [List.ofFn_succ,List.flatten_cons,listCells_append]
      rw [← children,ih,Fin.sum_univ_succ]

theorem children_arraySlots (n : ℕ) (traces : Fin n → Trace) :
    arraySlots (children n traces)=∑ j,arraySlots (traces j) := by
  induction n with
  | zero => simp [children,arraySlots]
  | succ n ih =>
      unfold children
      rw [List.ofFn_succ,List.flatten_cons,arraySlots_append]
      rw [← children,ih,Fin.sum_univ_succ]

theorem children_frames (n : ℕ) (traces : Fin n → Trace) (F : ℕ)
    (h : ∀ j,framePeak (traces j) ≤ F) : framePeak (children n traces) ≤ F := by
  induction n with
  | zero => simp [children,framePeak]
  | succ n ih =>
      unfold children
      rw [List.ofFn_succ,List.flatten_cons,framePeak_append]
      exact max_le (h 0) (ih (Fin.tail traces) (fun j => h j.succ))

def buildReference {α : Type*} (n : ℕ) (produce : Fin n → α × Trace) : FixedArrayTable n α × Trace :=
  (FixedArrayTable.ofFn (fun j => (produce j).1),
    [.frames (n+4),.arrayAllocation (2*(n+1)^2+8)] ++ under 2 (children n (fun j => (produce j).2)))

def build {α : Type*} (n : ℕ) (produce : Fin n → α × Trace) : FixedArrayTable n α × Trace :=
  let entries := List.ofFn produce
  (⟨(entries.map Prod.fst).toArray,by simp [entries]⟩,
    [.frames (n+4),.arrayAllocation (2*(n+1)^2+8)] ++ under 2 ((entries.map Prod.snd).flatten))

def packEntries {α : Type*} (n : ℕ) (items : List α) : Array α :=
  List.toArrayAux items (Array.mkEmpty n)

/-- Selected structural map: one cons per source cell, in source order.
It avoids the native `List.mapTR` accumulator/reversal path. -/
def mapDirect {α β : Type*} (f : α → β) : List α → List β
  | [] => []
  | item :: rest => f item :: mapDirect f rest

theorem mapDirect_eq_map {α β : Type*} (f : α → β) (items : List α) :
    mapDirect f items = items.map f := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [mapDirect,List.map_cons,ih]

theorem mapDirect_length {α β : Type*} (f : α → β) (items : List α) :
    (mapDirect f items).length = items.length := by
  rw [mapDirect_eq_map,List.length_map]

/-- Source interpreter for the selected structural map. Observer events are
ghost evidence; the reached map itself is `mapDirect`. -/
def mapDirectWithTrace {α β : Type*} (f : α → β) : List α → List β × Trace
  | [] => ([],[.frames 1])
  | item :: rest =>
      let later := mapDirectWithTrace f rest
      (f item :: later.1,[.frames 1,.listAllocation 1] ++ under 1 later.2)

theorem mapDirectWithTrace_state {α β : Type*} (f : α → β) (items : List α) :
    (mapDirectWithTrace f items).1 = mapDirect f items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [mapDirectWithTrace,mapDirect,ih]

theorem mapDirectWithTrace_bounds {α β : Type*} (f : α → β) (items : List α) :
    listCells (mapDirectWithTrace f items).2 = items.length ∧
    arraySlots (mapDirectWithTrace f items).2 = 0 ∧
    framePeak (mapDirectWithTrace f items).2 ≤ items.length+1 := by
  induction items with
  | nil => simp [mapDirectWithTrace,listCells,arraySlots,framePeak]
  | cons item rest ih =>
      have hu := framePeak_under 1 (mapDirectWithTrace f rest).2
      simp only [mapDirectWithTrace,listCells_append,arraySlots_append,framePeak_append,
        listCells,listCells_under,arraySlots,arraySlots_under,framePeak,List.length_cons]
      exact ⟨by omega,by omega,by omega⟩

theorem mapDirectWithTrace_cells {α β : Type*} (f : α → β) (items : List α) :
    listCells (mapDirectWithTrace f items).2 = items.length :=
  (mapDirectWithTrace_bounds f items).1

theorem mapDirectWithTrace_frames {α β : Type*} (f : α → β) (items : List α) :
    framePeak (mapDirectWithTrace f items).2 ≤ items.length+1 :=
  (mapDirectWithTrace_bounds f items).2.2

theorem packEntries_state {α : Type*} (n : ℕ) (items : List α) :
    packEntries n items = items.toArray := by
  apply Array.toList_inj.mp
  simp [packEntries,Array.toArrayAux_eq,Array.mkEmpty]

theorem packEntries_pushLoop {α : Type*} (n : ℕ) (items : List α) :
    packEntries n items =
      (NativeArrayConversionCore.pushLoop items (Array.mkEmpty n)).1 := by
  simp only [packEntries,NativeArrayConversionCore.pushLoop_state]

theorem packEntries_core {α : Type*} (n : ℕ) (items : List α) :
    packEntries n items = (NativeArrayConversionCore.pack items).1 := by
  rw [packEntries_state,NativeArrayConversionCore.pack_state]

def fromEntries {α : Type*} (n : ℕ) (entries : List (α × Trace))
    (hEntries : entries.length = n) : FixedArrayTable n α × Trace :=
  (⟨packEntries n (mapDirect Prod.fst entries),by rw [packEntries_state]; simp [mapDirect_length,hEntries]⟩,
    [.frames (n+4),.arrayAllocation (2*(n+1)^2+8)] ++
      under 2 (BinaryLifetimeFlattenList.flattenDirect (mapDirect Prod.snd entries)))

theorem fromEntries_ofFn {α : Type*} (n : ℕ) (produce : Fin n → α × Trace) :
    fromEntries n (List.ofFn produce) (by simp) = build n produce := by
  simp only [fromEntries,packEntries_state,mapDirect_eq_map,
    BinaryLifetimeFlattenList.flattenDirect_result,build]

theorem fromEntries_read {α : Type*} (n : ℕ) (entries : List (α × Trace))
    (hEntries : entries.length = n) (j : Fin n) :
    (fromEntries n entries hEntries).1.read j =
      (entries[j.val]'(by rw [hEntries]; exact j.isLt)).1 := by
  simp [fromEntries,packEntries_state,mapDirect_eq_map,FixedArrayTable.read]

def mapWithVisits {α β : Type*} (f : α → β) : List α → List β × ℕ
  | [] => ([],0)
  | item::rest =>
      let later := mapWithVisits f rest
      (f item::later.1,later.2+1)

theorem mapWithVisits_state {α β : Type*} (f : α → β) (items : List α) :
    (mapWithVisits f items).1 = items.map f := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [mapWithVisits,List.map_cons,ih]

theorem mapWithVisits_visits {α β : Type*} (f : α → β) (items : List α) :
    (mapWithVisits f items).2 = items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [mapWithVisits,List.length_cons,ih]

theorem fromEntries_projection_visits {α : Type*} (n : ℕ) (entries : List (α × Trace))
    (hEntries : entries.length = n) :
    (mapWithVisits Prod.fst entries).2 + (mapWithVisits Prod.snd entries).2 = 2*n := by
  simp only [mapWithVisits_visits,hEntries]
  omega

theorem build_reference {α : Type*} (n : ℕ) (produce : Fin n → α × Trace) :
    build n produce = buildReference n produce := by
  apply Prod.ext
  · apply BinaryOverlapInputPreparation.table_ext
    intro j
    simp [build,buildReference,FixedArrayTable.read_ofFn,List.map_ofFn,Function.comp_def]
    change (FixedArrayTable.ofFn (fun x : Fin n => (produce x).1)).read j = (produce j).1
    exact FixedArrayTable.read_ofFn _ _
  · simp only [build,buildReference,children,List.map_ofFn,Function.comp_def]

@[simp] theorem build_erases {α : Type*} (n : ℕ) (produce : Fin n → α × Trace) :
    (build n produce).1=FixedArrayTable.ofFn (fun j => (produce j).1) := by
  rw [build_reference]
  rfl

theorem build_bounds {α : Type*} (n : ℕ) (produce : Fin n → α × Trace) (B F : ℕ)
    (hB : ∀ j,listCells (produce j).2+arraySlots (produce j).2 ≤ B)
    (hF : ∀ j,framePeak (produce j).2 ≤ F) :
    listCells (build n produce).2+arraySlots (build n produce).2 ≤ n*B+2*(n+1)^2+8 ∧
    framePeak (build n produce).2 ≤ n+F+6 := by
  have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hB j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hSum
  have hFrame := children_frames n (fun j => (produce j).2) F hF
  have hUnder := framePeak_under 2 (children n (fun j => (produce j).2))
  rw [build_reference]
  simp only [buildReference,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under,children_listCells,children_arraySlots]
  exact ⟨by omega,by omega⟩

theorem build_all_prefix {α : Type*} (n : ℕ) (produce : Fin n → α × Trace) (B F : ℕ)
    (hB : ∀ j,listCells (produce j).2+arraySlots (produce j).2 ≤ B)
    (hF : ∀ j,framePeak (produce j).2 ≤ F) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (build n produce).2 steps ≤ borrowedCells+n*B+2*(n+1)^2+8 := by
  have hb := (build_bounds n produce B F hB hF).1
  have hl := listCells_take_le (build n produce).2 steps
  have ha := arraySlots_take_le (build n produce).2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryLifetimeArray
