import Blotto.GeneralPaperBasisSolveWork

/-! Fresh original point and next-coordinate direction with explicit
unit index primitives in every constructor. No earlier ray-test denominator
is reused; the arrays are exactly the native point/direction arrays.
-/
namespace Blotto.GeneralPaperBasisPreparationWork
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisPrefixSum
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def pointAssemble {j d : ℕ} (N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) :
    GeneralPaperBasisRationalSolve.RatVector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun k =>
    (if h : k.val<j then first.read ⟨k.val,h⟩ else (initial.read k:ℚ)/(N:ℚ),16))

theorem point_assemble_data {j d : ℕ} (N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) :
    (pointAssemble N first initial).1=(GeneralPaperBasisFreshPoint.assemble N first initial).1 := by
  simp only [pointAssemble,GeneralPaperBasisFreshPoint.assemble,PaperIndexedArrayConstruction.run_data]

theorem point_assemble_work {j d : ℕ} (N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) :
    (pointAssemble N first initial).2≤128*(d+1) := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun k : Fin d =>
    (if h : k.val<j then first.read ⟨k.val,h⟩ else (initial.read k:ℚ)/(N:ℚ),16))
  change (pointAssemble N first initial).2=(GeneralPaperBasisFreshPoint.assemble N first initial).2+8*d+2 at hh
  have ho := GeneralPaperBasisFreshPoint.assemble_work N first initial
  omega

def point {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) : GeneralPaperBasisFreshPoint.Result d :=
  let rhs := GeneralPaperBasisSolveWork.rhsRun N betaN rows initial
  let first := GeneralPaperBasisSolveWork.run N D A rhs.1
  let assembled := pointAssemble N first.values initial
  ⟨assembled.1,rhs.2+first.work+assembled.2+12⟩

theorem point_data {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) :
    (point N betaN D A rows initial).point=(GeneralPaperBasisFreshPoint.run N betaN D A rows initial).point := by
  simp only [point,GeneralPaperBasisFreshPoint.run,GeneralPaperBasisSolveWork.rhs_data,GeneralPaperBasisSolveWork.data,point_assemble_data]

theorem point_work {j d : ℕ} (N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) :
    (point N betaN D A rows initial).work≤1024*(j+1)*(j+d+2) := by
  have hr := GeneralPaperBasisSolveWork.rhs_work N betaN rows initial
  have hs := GeneralPaperBasisSolveWork.work N D A (GeneralPaperBasisSolveWork.rhsRun N betaN rows initial).1
  have ha := point_assemble_work N (GeneralPaperBasisSolveWork.run N D A (GeneralPaperBasisSolveWork.rhsRun N betaN rows initial).1).values initial
  change _+(GeneralPaperBasisSolveWork.run N D A (GeneralPaperBasisSolveWork.rhsRun N betaN rows initial).1).work+
    (pointAssemble N (GeneralPaperBasisSolveWork.run N D A (GeneralPaperBasisSolveWork.rhsRun N betaN rows initial).1).values initial).2+12≤_
  nlinarith only [hr,hs,ha]

def columnRun {j d : ℕ} (rows : Rows j d) (next : Fin d) : Vector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i => ((rows.read i).coefficients.read next,4))

theorem column_data {j d : ℕ} (rows : Rows j d) (next : Fin d) :
    (columnRun rows next).1=(GeneralPaperBasisDirection.columnRun rows next).1 := by
  simp only [columnRun,GeneralPaperBasisDirection.columnRun,PaperIndexedArrayConstruction.run_data]

theorem column_work {j d : ℕ} (rows : Rows j d) (next : Fin d) : (columnRun rows next).2≤128*(j+1) := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun i : Fin j => ((rows.read i).coefficients.read next,4))
  change (columnRun rows next).2=(GeneralPaperBasisDirection.columnRun rows next).2+8*j+2 at hh
  have ho := GeneralPaperBasisDirection.column_work rows next
  omega

def directionAssemble {j d : ℕ} (first : GeneralPaperBasisRationalSolve.RatVector j) : GeneralPaperBasisRationalSolve.RatVector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun k =>
    (if h : k.val<j then -(first.read ⟨k.val,h⟩) else if k.val=j then 1 else 0,16))

theorem direction_assemble_data {j d : ℕ} (first : GeneralPaperBasisRationalSolve.RatVector j) :
    (directionAssemble (d:=d) first).1=(GeneralPaperBasisDirection.assemble (d:=d) first).1 := by
  simp only [directionAssemble,GeneralPaperBasisDirection.assemble,PaperIndexedArrayConstruction.run_data]

theorem direction_assemble_work {j d : ℕ} (first : GeneralPaperBasisRationalSolve.RatVector j) :
    (directionAssemble (d:=d) first).2≤128*(d+1) := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun k : Fin d =>
    (if h : k.val<j then -(first.read ⟨k.val,h⟩) else if k.val=j then 1 else 0,16))
  change (directionAssemble (d:=d) first).2=(GeneralPaperBasisDirection.assemble (d:=d) first).2+8*d+2 at hh
  have ho := GeneralPaperBasisDirection.assemble_work (d:=d) first
  omega

def direction {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) : GeneralPaperBasisDirection.Result d :=
  let u := columnRun rows next
  let first := GeneralPaperBasisSolveWork.run 1 D A u.1
  let assembled := directionAssemble first.values
  ⟨assembled.1,u.2+first.work+assembled.2+12⟩

theorem direction_data {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) :
    (direction D A rows next).velocity=(GeneralPaperBasisDirection.run D A rows next).velocity := by
  simp only [direction,GeneralPaperBasisDirection.run,column_data,GeneralPaperBasisSolveWork.data,direction_assemble_data]

theorem direction_work {j d : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) :
    (direction D A rows next).work≤1024*(j+1)*(j+d+2) := by
  have hc := column_work rows next
  have hs := GeneralPaperBasisSolveWork.work 1 D A (columnRun rows next).1
  have ha := direction_assemble_work (d:=d) (GeneralPaperBasisSolveWork.run 1 D A (columnRun rows next).1).values
  change _+(GeneralPaperBasisSolveWork.run 1 D A (columnRun rows next).1).work+
    (directionAssemble (d:=d) (GeneralPaperBasisSolveWork.run 1 D A (columnRun rows next).1).values).2+12≤_
  nlinarith only [hc,hs,ha]

end Blotto.GeneralPaperBasisPreparationWork
