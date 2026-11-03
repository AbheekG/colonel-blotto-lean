import Blotto.ReferenceArrayBuilder
import Blotto.FixedArrayTable

/-! A reference-table implementation of the sized table's patch loop.
One write may copy every old reference. Its price also covers address/index
control; it does not copy the immutable object addressed by that reference.
These are declared source bit costs, not Lean allocator or library costs. -/

namespace Blotto.ReferenceTablePatchCost
set_option autoImplicit false

def writeWork (primitive : ℕ → ℕ) (addressWidth n : ℕ) (index : Fin n) : ℕ :=
  ReferenceArrayBuilder.pushWork primitive addressWidth n+
    2*addressWidth+4*primitive (binaryWordWidth (index.val+1))+10

def writeBound (c addressWidth n : ℕ) : ℕ :=
  (n+1)*(4*addressWidth+4*c*(binaryWordWidth (n+1)+1)+12)+
    2*addressWidth+4*c*binaryWordWidth (n+1)+10

theorem write_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (addressWidth n : ℕ) (index : Fin n) :
    writeWork primitive addressWidth n index ≤ writeBound c addressWidth n := by
  have hp := ReferenceArrayBuilder.push_work_bound primitive c hPrimitive addressWidth n n le_rfl
  have hi := (hPrimitive (binaryWordWidth (index.val+1))).trans
    (Nat.mul_le_mul_left c (binaryWordWidth_mono (by omega : index.val+1 ≤ n+1)))
  unfold writeWork writeBound
  nlinarith only [hp,hi]

def run {n : ℕ} {α : Type*} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (table : FixedArrayTable n α) : List (Fin n × α) → FixedArrayTable n α × ℕ
  | [] => (table,1)
  | entry::rest =>
      let returned := run primitive addressWidth (table.write entry.1 entry.2) rest
      (returned.1,writeWork primitive addressWidth n entry.1+returned.2)

theorem run_data {n : ℕ} {α : Type*} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (table : FixedArrayTable n α) (entries : List (Fin n × α)) :
    (run primitive addressWidth table entries).1 = table.patch entries := by
  induction entries generalizing table with
  | nil => rfl
  | cons entry rest ih => exact ih (table.write entry.1 entry.2)

theorem run_values_mem {n : ℕ} {α : Type*} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (table : FixedArrayTable n α) (entries : List (Fin n × α)) (pool : List α)
    (hTable : ∀ j, table.read j ∈ pool) (hEntries : ∀ entry ∈ entries, entry.2 ∈ pool) :
    ∀ j, (run primitive addressWidth table entries).1.read j ∈ pool := by
  induction entries generalizing table with
  | nil => exact hTable
  | cons entry rest ih =>
      apply ih (table.write entry.1 entry.2)
      · intro j
        rw [FixedArrayTable.read_write]
        split
        · exact hEntries entry (List.mem_cons_self)
        · exact hTable j
      · intro next hNext
        exact hEntries next (List.mem_cons_of_mem _ hNext)

theorem run_work_bound {n : ℕ} {α : Type*} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (addressWidth : ℕ)
    (table : FixedArrayTable n α) (entries : List (Fin n × α)) :
    (run primitive addressWidth table entries).2 ≤ entries.length*writeBound c addressWidth n+1 := by
  induction entries generalizing table with
  | nil => simp only [run,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons entry rest ih =>
      have hr := ih (table.write entry.1 entry.2)
      have hw := write_work_bound primitive c hPrimitive addressWidth n entry.1
      simp only [run,List.length_cons]
      nlinarith only [hr,hw]

theorem index_width_le_pool (n W : ℕ) :
    binaryWordWidth (n+1) ≤ StoredArrayReferenceList.poolAddressWidth n W := by
  apply binaryWordWidth_mono
  simp only [Nat.mul_add,Nat.mul_one]
  omega

theorem write_bound_of_index_width (c n A : ℕ) (hw : binaryWordWidth (n+1) ≤ A) :
    writeBound c A n ≤ (8*c+28)*(n+1)*(A+1) := by
  have h1 := Nat.mul_le_mul_left (n+1) (Nat.mul_le_mul_left (4*c) (Nat.add_le_add_right hw 1))
  have h2 := Nat.mul_le_mul_left (4*c) hw
  unfold writeBound
  change _ ≤ (8*c+28)*(n+1)*(A+1)
  calc
    _ ≤ (n+1)*(4*A+4*c*(A+1)+12)+2*A+4*c*A+10 := by nlinarith only [h1,h2]
    _ ≤ _ := by ring_nf; omega

theorem pool_write_bound (c n W : ℕ) :
    writeBound c (StoredArrayReferenceList.poolAddressWidth n W) n ≤
      (8*c+28)*(n+1)*(StoredArrayReferenceList.poolAddressWidth n W+1) :=
  write_bound_of_index_width c n _ (index_width_le_pool n W)

theorem pool_run_work_bound {n : ℕ} {α : Type*} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (W : ℕ)
    (table : FixedArrayTable n α) (entries : List (Fin n × α)) :
    (run primitive (StoredArrayReferenceList.poolAddressWidth n W) table entries).2 ≤
      entries.length*((8*c+28)*(n+1)*(StoredArrayReferenceList.poolAddressWidth n W+1))+1 :=
  (run_work_bound primitive c hPrimitive _ table entries).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left entries.length (pool_write_bound c n W)) 1)

end Blotto.ReferenceTablePatchCost
