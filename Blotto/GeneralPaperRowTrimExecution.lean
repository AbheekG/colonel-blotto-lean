import Blotto.GeneralPaperActualOrderedRootPrice

/-! Materialize the decoded list once, check retained array size once and
copy the first m references by an indexed fill. Resize only transports the
descriptor; it never copies entries or reconstructs a weighted-field list. -/
namespace Blotto.GeneralPaperRowTrimExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

def copyPrefix {α : Type*} (index : ℕ → ℕ) (A m : ℕ) (data : Array α) (hm : m≤data.size) : FixedArrayTable m α × ℕ :=
  PaperIndexedArrayConstruction.run index A (fun i : Fin m => (data[i.val]'(i.isLt.trans_le hm),64*A))

theorem copy_data {α : Type*} (index : ℕ → ℕ) (A m : ℕ) (data : Array α) (hm : m≤data.size) :
    (copyPrefix index A m data hm).1.data=data.extract 0 m := by
  rw [copyPrefix,PaperIndexedArrayConstruction.run_data]
  apply Array.ext
  · simp only [FixedArrayTable.ofFn,Array.size_ofFn,Array.size_extract,Nat.min_eq_left hm,Nat.sub_zero]
  · intro i hi hj
    simp only [FixedArrayTable.ofFn,Array.getElem_ofFn,Array.getElem_extract,Nat.zero_add]

def run {α : Type*} (index : ℕ → ℕ) (A m : ℕ) (labels : List α) : Option (FixedArrayTable m α) × ℕ :=
  let packed := PaperListReferenceArray.run index A labels
  let checked := GeneralPaperIntegerWordPrice.compare index m packed.1.size
  if hm : m≤packed.1.size then
    let copied := copyPrefix index A m packed.1 hm
    (some copied.1,packed.2+copied.2+checked+64*A)
  else (none,packed.2+checked+64*A)

theorem data {α : Type*} (index : ℕ → ℕ) (A m : ℕ) (labels : List α) :
    (run index A m labels).1=GeneralPaperRowPrefix.trim m labels := by
  unfold run GeneralPaperRowPrefix.trim
  dsimp only
  rw [PaperListReferenceArray.data]
  split
  · rename_i hm
    cases hrow : (copyPrefix index A m labels.toArray hm).1 with
    | mk copied hc =>
      have hd := copy_data index A m labels.toArray hm
      rw [hrow] at hd
      dsimp only at hd
      cases hd
      rfl
  · rfl

def resize {α : Type*} {n m : ℕ} (W : ℕ) (h : n=m) (row : FixedArrayTable n α) : FixedArrayTable m α × ℕ :=
  (GeneralPaperRowPrefix.resize h row,64*W)

theorem resize_data {α : Type*} {n m : ℕ} (W : ℕ) (h : n=m) (row : FixedArrayTable n α) :
    (resize W h row).1=GeneralPaperRowPrefix.resize h row := rfl

theorem trim_resize {α : Type*} {n m : ℕ} (h : n=m) (labels : List α) :
    (GeneralPaperRowPrefix.trim n labels).map (GeneralPaperRowPrefix.resize h)=GeneralPaperRowPrefix.trim m labels := by
  cases h
  cases hs : GeneralPaperRowPrefix.trim n labels with
  | none => rfl
  | some row => cases row; rfl

end Blotto.GeneralPaperRowTrimExecution
