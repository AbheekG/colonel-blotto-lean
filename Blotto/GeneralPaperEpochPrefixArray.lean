import Blotto.GeneralPaperEpochBatchArrays

/-! A linear running-sum traversal constructs the cached native prefix
array. Reference take/sum expressions occur only in its data specification;
the implementation does not rescan a prefix for every output entry.
-/
namespace Blotto.GeneralPaperEpochPrefixArray
set_option autoImplicit false
set_option maxHeartbeats 3000000

def scan (total : ℕ) : List ℕ → List ℕ
  | [] => [total]
  | value::rest => total::scan (total+value) rest

theorem scan_length (values : List ℕ) (total : ℕ) : (scan total values).length=values.length+1 := by
  induction values generalizing total with
  | nil => rfl
  | cons value rest ih => simp only [scan,List.length_cons,ih]

theorem scan_get (values : List ℕ) (total : ℕ) (i : Fin (values.length+1)) :
    (scan total values)[i.val]'(by rw [scan_length]; exact i.isLt)=total+(values.take i.val).sum := by
  induction values generalizing total with
  | nil =>
    have hi : i.val=0 := by have := i.isLt; simp only [List.length_nil] at *; omega
    simp only [hi,scan,List.getElem_cons_zero,List.take_zero,List.sum_nil,Nat.add_zero]
  | cons value rest ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,scan,List.getElem_cons_zero,List.take_zero,List.sum_nil,Nat.add_zero]
    · simp only [Fin.val_succ,scan,List.getElem_cons_succ,List.take_succ_cons,List.sum_cons]
      rw [ih (total+value) j]
      omega

def build {n : ℕ} (values : FixedArrayTable n ℕ) : FixedArrayTable (n+1) ℕ :=
  ⟨(scan 0 values.data.toList).toArray,by simp only [List.size_toArray,scan_length,Array.length_toList,values.size]⟩

theorem read_build {n : ℕ} (values : FixedArrayTable n ℕ) (i : Fin (n+1)) :
    (build values).read i=(values.data.toList.take i.val).sum := by
  have he := scan_get values.data.toList 0 ⟨i.val,by simpa only [Array.length_toList,values.size] using i.isLt⟩
  simpa only [build,FixedArrayTable.read,List.getElem_toArray,Nat.zero_add] using he

theorem read_zero {n : ℕ} (values : FixedArrayTable n ℕ) : (build values).read 0=0 := by
  rw [read_build]
  rfl

theorem read_succ {n : ℕ} (values : FixedArrayTable n ℕ) (i : Fin n) :
    (build values).read i.succ=(build values).read i.castSucc+values.read i := by
  rw [read_build,read_build]
  have hi : i.val<values.data.toList.length := by simpa only [Array.length_toList,values.size] using i.isLt
  rw [show i.succ.val=i.val+1 by rfl,List.take_succ_eq_append_getElem hi,List.sum_append]
  simp only [List.sum_singleton,Fin.val_castSucc,Array.getElem_toList,FixedArrayTable.read]

theorem read_total {n : ℕ} (values : FixedArrayTable n ℕ) :
    (build values).read (Fin.last n)=values.data.toList.sum := by
  rw [read_build]
  simp only [Fin.val_last,List.take_of_length_le (by rw [Array.length_toList,values.size])]

end Blotto.GeneralPaperEpochPrefixArray
