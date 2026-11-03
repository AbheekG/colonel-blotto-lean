import Blotto.GeneralPaperBasisFreshPointUnique

/-! Native next-coordinate-one direction. A fresh cached adjugate solve
uses the original next column; old velocities are its negatives, the next
velocity is one, and all later velocities are zero.
-/
namespace Blotto.GeneralPaperBasisDirection
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisPrefixSum
set_option autoImplicit false
set_option maxHeartbeats 3000000

def columnRun {j d : ℕ} (rows : Rows j d) (next : Fin d) : Vector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun i => ((rows.read i).coefficients.read next,4))

def assemble {j d : ℕ} (first : GeneralPaperBasisRationalSolve.RatVector j) : GeneralPaperBasisRationalSolve.RatVector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun k =>
    (if h : k.val<j then -(first.read ⟨k.val,h⟩) else if k.val=j then 1 else 0,16))

structure Result (d : ℕ) where
  velocity : GeneralPaperBasisRationalSolve.RatVector d
  work : ℕ

def run {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) : Result d :=
  let u := columnRun rows next
  let first := GeneralPaperBasisRationalSolve.run 1 D A u.1
  let velocity := assemble first.values
  ⟨velocity.1,u.2+first.work+velocity.2+12⟩

theorem column_read {j d : ℕ} (rows : Rows j d) (next : Fin d) (i : Fin j) :
    (columnRun rows next).1.read i=(rows.read i).coefficients.read next := by
  simp only [columnRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem first_read {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) (hj : j≤d) (i : Fin j) :
    (run D A rows next).velocity.read (embed hj i)=
      -((GeneralPaperBasisRationalSolve.run 1 D A (columnRun rows next).1).values.read i) := by
  simp only [run,assemble,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  change (if h : i.val<j then -((GeneralPaperBasisRationalSolve.run 1 D A (columnRun rows next).1).values.read ⟨i.val,h⟩) else _)=_
  rw [dite_eq_left i.isLt]

theorem next_read {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) (hNext : next.val=j) :
    (run D A rows next).velocity.read next=1 := by
  simp only [run,assemble,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  rw [dite_eq_right (show ¬next.val<j by omega),ite_eq_left hNext]

theorem later_read {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) (k : Fin d) (hk : j<k.val) :
    (run D A rows next).velocity.read k=0 := by
  simp only [run,assemble,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  rw [dite_eq_right (show ¬k.val<j by omega),ite_eq_right (show k.val≠j by omega)]

theorem column_work {j d : ℕ} (rows : Rows j d) (next : Fin d) : (columnRun rows next).2≤64*(j+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun i : Fin j => ((rows.read i).coefficients.read next,4))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  change (columnRun rows next).2≤_ at hh
  omega

theorem assemble_work {j d : ℕ} (first : GeneralPaperBasisRationalSolve.RatVector j) :
    (assemble (d := d) first).2≤64*(d+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun k : Fin d => (if h : k.val<j then -(first.read ⟨k.val,h⟩) else if k.val=j then (1:ℚ) else 0,16))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  change (assemble (d := d) first).2≤_ at hh
  omega

theorem work {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) :
    (run D A rows next).work≤512*(j+1)*(j+d+2) := by
  have hc := column_work rows next
  have hs := GeneralPaperBasisRationalSolve.work 1 D A (columnRun rows next).1
  have ha := assemble_work (d := d) (GeneralPaperBasisRationalSolve.run 1 D A (columnRun rows next).1).values
  change (columnRun rows next).2+(GeneralPaperBasisRationalSolve.run 1 D A (columnRun rows next).1).work+
    (assemble (d := d) (GeneralPaperBasisRationalSolve.run 1 D A (columnRun rows next).1).values).2+12≤_
  nlinarith only [hc,hs,ha]

end Blotto.GeneralPaperBasisDirection
