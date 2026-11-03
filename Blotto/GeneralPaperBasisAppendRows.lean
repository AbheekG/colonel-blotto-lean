import Blotto.GeneralPaperBasisOriginalDirection

/-! Native last-slot extension of retained original rows. Its first j+1
columns are precisely the border used by the stored integer update.
-/
namespace Blotto.GeneralPaperBasisAppendRows
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisDenseRow
open GeneralPaperBasisPrefixSum GeneralPaperBasisAppendIndex GeneralPaperBasisOriginalDirection
set_option autoImplicit false
set_option maxHeartbeats 3500000

def append {j d : ℕ} (rows : Rows j d) (new : Dense d) : Rows (j+1) d :=
  FixedArrayTable.ofFn (fun i => if h : i.val<j then rows.read ⟨i.val,h⟩ else new)

theorem old_read {j d : ℕ} (rows : Rows j d) (new : Dense d) (i : Fin j) :
    (append rows new).read i.castSucc=rows.read i := by
  simp only [append,FixedArrayTable.read_ofFn]
  exact dite_eq_left i.isLt

theorem last_read {j d : ℕ} (rows : Rows j d) (new : Dense d) :
    (append rows new).read (encode j none)=new := by
  simp only [append,FixedArrayTable.read_ofFn,encode,lt_self_iff_false,dite_false]

theorem read_option {j d : ℕ} (rows : Rows j d) (new : Dense d) (i : Option (Fin j)) :
    (append rows new).read (encode j i)=(match i with | none => new | some k => rows.read k) := by
  cases i with
  | none => exact last_read rows new
  | some k => exact old_read rows new k

theorem minor_border {j d : ℕ} (rows : Rows j d) (new : Dense d) (hj : j≤d)
    (hNew : j+1≤d) (next : Fin d) (hNext : next.val=j) :
    minor (append rows new) hNew=
      GeneralPaperBasisStoredCorrect.extended (minor rows hj)
        (GeneralPaperBasisDirection.columnRun rows next).1 (rowPrefix new hj) (new.coefficients.read next) := by
  have hcNone : embed hNew (encode j none)=next := Fin.ext hNext.symm
  have hcSome (k : Fin j) : embed hNew (encode j (some k))=embed hj k := rfl
  have hh : (minor (append rows new) hNew).submatrix (encode j) (encode j)=
      GeneralPaperBasisBorder.border (minor rows hj)
        (GeneralPaperBasisDirection.columnRun rows next).1.read (rowPrefix new hj).read
        (new.coefficients.read next) := by
    ext i k
    change ((append rows new).read (encode j i)).coefficients.read (embed hNew (encode j k))=_
    rw [read_option]
    cases i <;> cases k <;>
      simp only [GeneralPaperBasisBorder.border,hcNone,hcSome,GeneralPaperBasisDirection.column_read,
        rowPrefix,FixedArrayTable.read_ofFn,minor]
  unfold GeneralPaperBasisStoredCorrect.extended
  rw [←hh]
  ext i k
  simp only [Matrix.submatrix_apply,encode_decode]

end Blotto.GeneralPaperBasisAppendRows
