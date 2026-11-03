import Blotto.BinaryLifetimeArrayMeasured
import Blotto.BinaryTerminalPhysicalRouteLifetime

/-! Cache table preparation executes structural enumeration, one value map and
the actual preallocated push loop. The old blank-child builder record is exact;
its enumeration/map/packing source charge is returned, without replaying an old
builder or constructing discarded child traces. Native index/reference/metadata
bit pricing and physical ownership/allocator/GC costs remain separate. -/
namespace Blotto.BinaryCacheTableMeasured
open BinarySeedPreparationSpace BinaryRationalNormalization
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def build {α : Type*} (n : ℕ) (produce : Fin n → α) : (FixedArrayTable n α × Trace) × ℕ :=
  let entries := BinaryLifetimeArrayMeasured.enumerate n (fun j => ((produce j,[]),4))
  let values := BinaryLifetimeArray.mapWithVisits Prod.fst entries.1
  let packed := BinaryLifetimeArrayMeasured.pack values.1 (Array.mkEmpty n)
  have hSize : packed.1.size = n := by
    simp [packed,BinaryLifetimeArrayMeasured.pack_state,values,entries,
      BinaryLifetimeArray.mapWithVisits_state,BinaryLifetimeArrayMeasured.enumerate_state]
  ((⟨packed.1,hSize⟩,[.frames (n+4),.arrayAllocation (2*(n+1)^2+8)]),
    entries.2+4*values.2+packed.2+8)

theorem build_data {α : Type*} (n : ℕ) (produce : Fin n → α) :
    (build n produce).1.1 = (BinaryLifetimeArray.build n (fun j => (produce j,[]))).1 :=
  BinaryLifetimeArrayMeasured.build_data n (fun j => ((produce j,[]),4))

theorem build_compat {α : Type*} (n : ℕ) (produce : Fin n → α) :
    (build n produce).1 = BinaryLifetimeArray.build n (fun j => (produce j,[])) := by
  apply Prod.ext
  · exact build_data n produce
  · simp [build,BinaryLifetimeArray.build,List.map_ofFn,Function.comp_def,under]

theorem build_work {α : Type*} (n : ℕ) (produce : Fin n → α) :
    (build n produce).2 ≤ 72*(n+1)^2 := by
  have h := BinaryLifetimeArrayMeasured.build_work_bound n (fun j => ((produce j,[]),4)) 4 (fun _ => le_rfl)
  change (build n produce).2 ≤ _ at h
  nlinarith

def packTable {α : Type*} (items : List α) : FixedArrayTable items.length α × ℕ :=
  let packed := BinaryLifetimeArrayMeasured.pack items (Array.mkEmpty items.length)
  (⟨packed.1,by
    change (BinaryLifetimeArrayMeasured.pack items (Array.mkEmpty items.length)).1.size = items.length
    rw [BinaryLifetimeArrayMeasured.pack_empty_state]
    simp⟩,packed.2)

theorem packTable_data {α : Type*} (items : List α) :
    (packTable items).1 = (⟨items.toArray,by simp⟩ : FixedArrayTable items.length α) := by
  simp only [packTable,BinaryLifetimeArrayMeasured.pack_empty_state]

theorem packTable_work {α : Type*} (items : List α) :
    (packTable items).2 ≤ 16*(items.length+1)^2 := by
  have h := BinaryLifetimeArrayMeasured.pack_bound items (Array.mkEmpty items.length) items.length (by simp)
  change (packTable items).2 ≤ _ at h
  nlinarith

def indices (n : ℕ) : List (Fin n) × ℕ :=
  let entries := BinaryLifetimeArrayMeasured.enumerate n (fun j => ((j,[]),4))
  let values := BinaryLifetimeArray.mapWithVisits Prod.fst entries.1
  (values.1,entries.2+4*values.2+4)

theorem indices_data (n : ℕ) : (indices n).1 = List.finRange n := by
  simp only [indices,BinaryLifetimeArray.mapWithVisits_state,BinaryLifetimeArrayMeasured.enumerate_state,
    List.map_ofFn,Function.comp_def]
  exact List.ofFn_id n

theorem indices_work (n : ℕ) : (indices n).2 ≤ 32*(n+1)^2 := by
  have he := BinaryLifetimeArrayMeasured.enumerationCharge_bound n
  simp only [indices,BinaryLifetimeArrayMeasured.enumerate_work,
    BinaryLifetimeArray.mapWithVisits_visits,BinaryLifetimeArrayMeasured.enumerate_state,
    List.length_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  nlinarith

def initial (n m : ℕ) : (FixedArrayTable n (BinaryGroupRoutes.Route m) × Trace) × ℕ :=
  build n (fun _ => (none,BinaryRationalOpcode.zero))

theorem initial_compat (n m : ℕ) : (initial n m).1 =
    BinaryTerminalPhysicalRouteLifetime.initialRoutesWithTrace n m := build_compat _ _

theorem initial_work (n m : ℕ) : (initial n m).2 ≤ 72*(n+1)^2 := build_work _ _

def totals {n m : ℕ} (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    (FixedArrayTable m SignedWord × Trace) × ℕ := build m (fun g => (packing.read g).2)

theorem totals_compat {n m : ℕ} (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    (totals packing).1 = BinaryTerminalPhysicalRouteLifetime.totalsWithTrace packing := build_compat _ _

theorem totals_work {n m : ℕ} (packing : FixedArrayTable m (List (Fin n) × SignedWord)) :
    (totals packing).2 ≤ 72*(m+1)^2 := build_work _ _

def write {n : ℕ} {α : Type*} (table : FixedArrayTable n α) (j : Fin n) (value : α) :
    FixedArrayTable n α × ℕ :=
  let copied := build n (fun i => if i=j then value else table.read i)
  (copied.1.1,copied.2)

theorem write_data {n : ℕ} {α : Type*} (table : FixedArrayTable n α) (j : Fin n) (value : α) :
    (write table j value).1 = table.write j value := by
  apply BinaryOverlapInputPreparation.table_ext
  intro i
  simp only [write,build_data,BinaryLifetimeArray.build_erases,FixedArrayTable.read_ofFn,
    FixedArrayTable.read_write]

theorem write_work {n : ℕ} {α : Type*} (table : FixedArrayTable n α) (j : Fin n) (value : α) :
    (write table j value).2 ≤ 72*(n+1)^2 := build_work _ _

end Blotto.BinaryCacheTableMeasured
