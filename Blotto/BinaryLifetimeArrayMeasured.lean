import Blotto.BinaryLifetimeArray
import Blotto.BinaryPRGHeapTraceUsage

/-! Each callback is reached once and its returned data/trace/work is retained.
Structural enumeration, projection and packing have explicit control/reference
reservations, including a full old-array copy allowance per push. These are
source reference-slot charges; native bit/address/ownership/observer/allocator
realization is separate. The enlarged trace includes enumeration activations. -/

namespace Blotto.BinaryLifetimeArrayMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def enumerate {α : Type*} : (n : ℕ) → (Fin n → (α × Trace) × ℕ) → List (α × Trace) × ℕ
  | 0,_ => ([],4)
  | n+1,produce =>
      let first := produce 0
      let later := enumerate n (fun j => produce j.succ)
      (first.1::later.1,first.2+later.2+(n+1)+8)

def enumerationCharge : ℕ → ℕ
  | 0 => 4
  | n+1 => enumerationCharge n+(n+1)+8

theorem enumerate_state {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) :
    (enumerate n produce).1 = List.ofFn (fun j => (produce j).1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [enumerate,List.ofFn_succ,ih,Fin.tail]

theorem enumerate_work {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) :
    (enumerate n produce).2 = (∑ j, (produce j).2)+enumerationCharge n := by
  induction n with
  | zero => simp [enumerate,enumerationCharge]
  | succ n ih => simp only [enumerate,enumerationCharge,ih,Fin.sum_univ_succ]; omega

theorem enumerationCharge_bound (n : ℕ) : enumerationCharge n ≤ 16*(n+1)^2 := by
  induction n with
  | zero => decide
  | succ n ih => simp only [enumerationCharge]; nlinarith

def pack {α : Type*} : List α → Array α → Array α × ℕ
  | [],acc => (acc,4)
  | item::rest,acc =>
      let later := pack rest (acc.push item)
      (later.1,acc.size+later.2+9)

theorem pack_state {α : Type*} (items : List α) (acc : Array α) :
    (pack items acc).1 = List.toArrayAux items acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => exact ih (acc.push item)

theorem pack_core {α : Type*} (items : List α) (acc : Array α) :
    (pack items acc).1 = (NativeArrayConversionCore.pushLoop items acc).1 := by
  rw [pack_state,NativeArrayConversionCore.pushLoop_state]

theorem pack_empty_state {α : Type*} (items : List α) (n : ℕ) :
    (pack items (Array.mkEmpty n)).1 = items.toArray := by
  apply Array.toList_inj.mp
  simp [pack_state,Array.toArrayAux_eq,Array.mkEmpty]

theorem pack_bound {α : Type*} (items : List α) (acc : Array α) (B : ℕ)
    (hSize : acc.size+items.length ≤ B) : (pack items acc).2 ≤ items.length*(B+9)+4 := by
  induction items generalizing acc with
  | nil => simp [pack]
  | cons item rest ih =>
      have hLater := ih (acc.push item) (by simp only [Array.size_push,List.length_cons] at *; omega)
      simp only [pack,List.length_cons]
      have hAcc : acc.size ≤ B := by simp only [List.length_cons] at hSize; omega
      nlinarith

def storageReserve (n : ℕ) : ℕ := 32*(n+1)^2+64

def build {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) : (FixedArrayTable n α × Trace) × ℕ :=
  let entries := enumerate n produce
  let values := BinaryLifetimeArray.mapWithVisits Prod.fst entries.1
  let packed := pack values.1 (Array.mkEmpty n)
  have hSize : packed.1.size = n := by
    simp [packed,pack_state,values,entries,BinaryLifetimeArray.mapWithVisits_state,enumerate_state]
  ((⟨packed.1,hSize⟩,[.frames (2*n+8),.arrayAllocation (storageReserve n)]++
    under (n+2) (BinaryLifetimeFlattenList.flattenDirect (BinaryLifetimeArray.mapDirect Prod.snd entries.1))),
    entries.2+4*values.2+packed.2+8)

theorem build_data {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) :
    (build n produce).1.1 = (BinaryLifetimeArray.build n (fun j => (produce j).1)).1 := by
  have hData : (build n produce).1.1.data =
      (BinaryLifetimeArray.build n (fun j => (produce j).1)).1.data := by
    change (pack (BinaryLifetimeArray.mapWithVisits Prod.fst (enumerate n produce).1).1
      (Array.mkEmpty n)).1 = _
    rw [pack_empty_state _ n,BinaryLifetimeArray.build_erases]
    simp only [BinaryLifetimeArray.mapWithVisits_state,enumerate_state,List.map_ofFn,
      Function.comp_def,List.toArray_ofFn,FixedArrayTable.ofFn]
  have hExt : ∀ a b : FixedArrayTable n α,a.data = b.data → a = b := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  exact hExt _ _ hData

theorem build_trace {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) :
    (build n produce).1.2 = [.frames (2*n+8),.arrayAllocation (storageReserve n)]++
      under (n+2) (BinaryLifetimeArray.children n (fun j => (produce j).1.2)) := by
  simp only [build,BinaryLifetimeArray.mapDirect_eq_map,enumerate_state,
    BinaryLifetimeFlattenList.flattenDirect_result,List.map_ofFn,Function.comp_def,BinaryLifetimeArray.children]

theorem build_work {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) :
    (build n produce).2 ≤ (∑ j, (produce j).2)+64*(n+1)^2 := by
  let entries := (enumerate n produce).1
  let values := BinaryLifetimeArray.mapWithVisits Prod.fst entries
  have hLength : entries.length = n := by simp [entries,enumerate_state]
  have hValues : values.1.length = n := by simp [values,BinaryLifetimeArray.mapWithVisits_state,hLength]
  have hPack := pack_bound values.1 (Array.mkEmpty n) n (by simp [hValues])
  have hVisits : values.2 = n := by simp [values,BinaryLifetimeArray.mapWithVisits_visits,hLength]
  have hEnum := enumerationCharge_bound n
  change (enumerate n produce).2+4*values.2+(pack values.1 (Array.mkEmpty n)).2+8 ≤ _
  rw [enumerate_work,hVisits]
  rw [hValues] at hPack
  nlinarith

theorem build_work_bound {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) (W : ℕ)
    (hWork : ∀ j,(produce j).2 ≤ W) : (build n produce).2 ≤ n*W+64*(n+1)^2 := by
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hWork j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hSum
  exact (build_work n produce).trans (Nat.add_le_add_right hSum _)

theorem build_bounds {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) (B F : ℕ)
    (hCells : ∀ j,BinaryPRGHeapPrimitiveLifetime.cells (produce j).1.2 ≤ B)
    (hFrames : ∀ j,framePeak (produce j).1.2 ≤ F) :
    usage (build n produce).1.2 ≤ n*B+storageReserve n+2*n+F+10 := by
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hCells j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    BinaryPRGHeapPrimitiveLifetime.cells,Finset.sum_add_distrib] at hSum
  have hFrame := BinaryLifetimeArray.children_frames n (fun j => (produce j).1.2) F hFrames
  have hUnder := framePeak_under (n+2) (BinaryLifetimeArray.children n (fun j => (produce j).1.2))
  rw [build_trace]
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells,listCells_append,arraySlots_append,
    listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak,
    BinaryLifetimeArray.children_listCells,BinaryLifetimeArray.children_arraySlots]
  omega

theorem build_all_prefix {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) (B F : ℕ)
    (hCells : ∀ j,BinaryPRGHeapPrimitiveLifetime.cells (produce j).1.2 ≤ B)
    (hFrames : ∀ j,framePeak (produce j).1.2 ≤ F) (borrowed steps : ℕ) :
    retainedHeap borrowed (build n produce).1.2 steps ≤ borrowed+(n*B+storageReserve n+2*n+F+10) ∧
      framePeak ((build n produce).1.2.take steps) ≤ n*B+storageReserve n+2*n+F+10 :=
  all_prefix _ _ (build_bounds n produce B F hCells hFrames) borrowed steps

end Blotto.BinaryLifetimeArrayMeasured
