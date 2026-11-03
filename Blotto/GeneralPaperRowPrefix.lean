import Blotto.GeneralPaperTagBudgetTransfer

/-! Linear native conversion of a decoded list to its leading sized row.
Convert the list once, test the native size once, and extract the prefix.
There are no repeated linked-list indexed reads in this program.
-/
namespace Blotto.GeneralPaperRowPrefix
set_option autoImplicit false

def trim {α : Type*} (m : ℕ) (labels : List α) : Option (FixedArrayTable m α) :=
  let data := labels.toArray
  if h : m≤data.size then
    some ⟨data.extract 0 m,by simp only [Array.size_extract,Nat.min_eq_left h,Nat.sub_zero]⟩
  else none

theorem trim_success {α : Type*} (m : ℕ) (labels : List α) (hLen : m≤labels.length) :
    ∃ row, trim m labels=some row := by
  dsimp only [trim]
  split
  · exact ⟨_,rfl⟩
  · rename_i h
    exact (h (by simpa only [List.size_toArray] using hLen)).elim

theorem trim_list {α : Type*} (m : ℕ) (labels : List α) (row : FixedArrayTable m α)
    (hTrim : trim m labels=some row) : row.data.toList=labels.take m := by
  dsimp only [trim] at hTrim
  split at hTrim
  · have he := Option.some.inj hTrim
    rw [←he]
    simp only [Array.toList_extract,List.toList_toArray,List.extract,Nat.sub_zero,List.drop_zero]
  · cases hTrim

theorem list_ofFn {α : Type*} {m : ℕ} (row : FixedArrayTable m α) : List.ofFn row.read=row.data.toList := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,Array.length_toList,row.size]
  · intro i hi hj
    simp only [List.getElem_ofFn,FixedArrayTable.read,Array.getElem_toList]

theorem trim_ofFn {α : Type*} (m : ℕ) (labels : List α) (row : FixedArrayTable m α)
    (hTrim : trim m labels=some row) : List.ofFn row.read=labels.take m :=
  (list_ofFn row).trans (trim_list m labels row hTrim)

def resize {α : Type*} {n m : ℕ} (h : n=m) (row : FixedArrayTable n α) : FixedArrayTable m α :=
  ⟨row.data,row.size.trans h⟩

theorem resize_data {α : Type*} {n m : ℕ} (h : n=m) (row : FixedArrayTable n α) :
    (resize h row).data=row.data := rfl

theorem resize_ofFn {α : Type*} {n m : ℕ} (h : n=m) (row : FixedArrayTable n α) :
    List.ofFn (resize h row).read=List.ofFn row.read := by
  rw [list_ofFn,list_ofFn]
  rfl

end Blotto.GeneralPaperRowPrefix
