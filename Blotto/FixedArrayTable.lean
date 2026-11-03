import Blotto.RationalResourceArray

/-! Sized native arrays with selected-entry writes. Patch traverses its
assignment list once; repeated writes are permitted when values agree. -/

namespace Blotto

structure FixedArrayTable (n : ℕ) (α : Type*) where
  data : Array α
  size : data.size = n

namespace FixedArrayTable

def read {n : ℕ} {α : Type*} (a : FixedArrayTable n α) (j : Fin n) : α :=
  a.data[j.val]'(by rw [a.size]; exact j.isLt)

def ofFn {n : ℕ} {α : Type*} (f : Fin n → α) : FixedArrayTable n α :=
  ⟨Array.ofFn f, Array.size_ofFn⟩

def write {n : ℕ} {α : Type*} (a : FixedArrayTable n α) (j : Fin n) (v : α) : FixedArrayTable n α :=
  ⟨a.data.set j.val v (by rw [a.size]; exact j.isLt), by simp [a.size]⟩

def patch {n : ℕ} {α : Type*} (a : FixedArrayTable n α) : List (Fin n × α) → FixedArrayTable n α
  | [] => a
  | e :: rest => (a.write e.1 e.2).patch rest

theorem read_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) (j : Fin n) : (ofFn f).read j = f j := by
  simp [read, ofFn]

theorem read_write {n : ℕ} {α : Type*} (a : FixedArrayTable n α) (i : Fin n) (v : α) (j : Fin n) :
    (a.write i v).read j = if j = i then v else a.read j := by
  simp [read, write, Array.getElem_set, Fin.ext_iff, eq_comm]

theorem read_patch {n : ℕ} {α : Type*} (a : FixedArrayTable n α) (es : List (Fin n × α))
    (f : Fin n → α) (hf : ∀ e ∈ es, e.2 = f e.1) (j : Fin n) :
    (a.patch es).read j = if j ∈ es.map Prod.fst then f j else a.read j := by
  induction es generalizing a with
  | nil => simp [patch]
  | cons e es ih =>
    have hv := hf e (by simp)
    have ht : ∀ e ∈ es, e.2 = f e.1 := fun e he => hf e (by simp [he])
    rw [patch, ih _ ht, read_write]
    by_cases hr : j ∈ es.map Prod.fst
    · simp [hr]
    · by_cases hj : j = e.1
      · simp [hj, hv]
      · simp [hr, hj]

theorem patch_preserves {n : ℕ} {α : Type*} (a : FixedArrayTable n α) (es : List (Fin n × α))
    (j : Fin n) (hj : j ∉ es.map Prod.fst) : (a.patch es).read j = a.read j := by
  induction es generalizing a with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hj
    rw [patch, ih _ hj.2, read_write, ite_eq_right hj.1]

theorem read_patch_at {n : ℕ} {α : Type*} (a : FixedArrayTable n α) (es : List (Fin n × α))
    (j : Fin n) (v : α) (hv : ∀ e ∈ es, e.1 = j → e.2 = v)
    (hj : j ∈ es.map Prod.fst) : (a.patch es).read j = v := by
  induction es generalizing a with
  | nil => simp at hj
  | cons e es ih =>
    by_cases ht : j ∈ es.map Prod.fst
    · rw [patch]
      exact ih _ (fun e he => hv e (by simp [he])) ht
    · have he : j = e.1 := by simpa [ht] using hj
      rw [patch, patch_preserves _ _ _ ht, read_write, ite_eq_left he]
      exact hv e (by simp) he.symm

end FixedArrayTable
end Blotto
