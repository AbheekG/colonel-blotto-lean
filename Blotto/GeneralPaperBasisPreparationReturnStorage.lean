import Blotto.GeneralPaperBasisAssemblyStorage

/-! Literal solve and full point/direction preparation returns. Complete
rational arrays, original scalar arguments and every enclosing native
phase/partial-price field are counted. Prior phase windows retain inputs,
RHS/numerators/division/assembly buffers and the complete original basis. -/
namespace Blotto.GeneralPaperBasisPreparationReturnStorage
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile array_bound)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def solvePrice (model : RationalCostModel) (W j R : ℕ) : ℕ := 1024*(j+1)^2*(W+model.rat R)
def solveCap (model : RationalCostModel) (W j R : ℕ) : ℕ := j+1+3*solvePrice model W j R+8*W
def solveWindow {j : ℕ} (model : RationalCostModel) (W N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) : ℕ :=
  let numerators := GeneralPaperBasisProductBits.mulVecRun model.rat W A rhs
  let values := GeneralPaperBasisDivideBits.run model.rat W N D numerators.1
  let result := GeneralPaperBasisSolveBits.run model.rat W N D A rhs
  arrayFootprint W rationalWordWidth result.values+natBits N+integerBits D+
    fields W [j,numerators.2,values.2,result.work,numerators.2+values.2,numerators.2+values.2+8*W,8*W]+192*W
def solveProfile (model : RationalCostModel) (W j R : ℕ) : ℕ := arrayProfile W j R+2*R+
  7*(natBits (solveCap model W j R)+W)+224*W

theorem solve_bound {j : ℕ} (model : RationalCostModel) (W N H X R : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j)
    (hD : D.natAbs≤H) (hA : ∀ i k,((A.read i).read k).natAbs≤H) (hr : ∀ i,(rhs.read i).natAbs≤X)
    (hR : GeneralPaperBasisSolveBits.width j N H X≤R) (hW : 1≤W) (hIndex : binaryWordWidth (j+1)≤W) :
    solveWindow model W N D A rhs≤solveProfile model W j R := by
  let numerators := GeneralPaperBasisProductBits.mulVecRun model.rat W A rhs
  let values := GeneralPaperBasisDivideBits.run model.rat W N D numerators.1
  let result := GeneralPaperBasisSolveBits.run model.rat W N D A rhs
  have hWidth := (GeneralPaperBasisSolveBits.component_widths j N H X).2.trans hR
  have hOutput := array_bound W R rationalWordWidth result.values (fun i =>
    (rationalWordWidth_of_height (GeneralPaperBasisSolveBits.result_height model.rat W N H X D A rhs hD hA hr i)).trans hWidth)
  have hN : natBits N≤R := by unfold natBits GeneralPaperBasisDivideBits.height at *; omega
  have hDet : integerBits D≤R := by have h := binaryWordWidth_mono hD; unfold integerBits GeneralPaperBasisDivideBits.height at *; omega
  have hWork := (GeneralPaperBasisSolveBits.work model.rat model.monotone W N H X hW hIndex D A rhs hD hA hr).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  change result.work≤solvePrice model W j R at hWork
  have hShape : result.work=numerators.2+values.2+8*W := rfl
  have hf := fields_bound W (natBits (solveCap model W j R))
    [j,numerators.2,values.2,result.work,numerators.2+values.2,numerators.2+values.2+8*W,8*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold solveCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (solveCap model W j R)+W)+32*W at hf
  unfold solveWindow solveProfile
  dsimp only
  dsimp only [numerators,values,result] at hOutput hf
  omega

def preparationPrice (model : RationalCostModel) (W j d R : ℕ) : ℕ := 4096*(j+1)*(j+d+2)*(W+model.rat R)
def preparationCap (model : RationalCostModel) (W j d R : ℕ) : ℕ := j+d+1+3*preparationPrice model W j d R+16*W
def pointWindow {j d : ℕ} (model : RationalCostModel) (W N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) : ℕ :=
  let rhs := GeneralPaperBasisRHSBits.run model.rat W N betaN rows initial
  let first := GeneralPaperBasisSolveBits.run model.rat W N D A rhs.1
  let values := GeneralPaperBasisAssemblyBits.pointRun model.rat W N first.values initial
  let result := GeneralPaperBasisPreparationBits.point model.rat W N betaN D A rows initial
  arrayFootprint W rationalWordWidth result.point+
    fields W [j,d,rhs.2,first.work,values.2,result.work,rhs.2+first.work,rhs.2+first.work+values.2,16*W]+256*W
def directionWindow {j d : ℕ} (model : RationalCostModel) (W : ℕ) (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) : ℕ :=
  let column := GeneralPaperBasisAssemblyBits.columnRun W rows next
  let first := GeneralPaperBasisSolveBits.run model.rat W 1 D A column.1
  let values := GeneralPaperBasisAssemblyBits.directionRun (d:=d) model.rat W first.values
  let result := GeneralPaperBasisPreparationBits.direction model.rat W D A rows next
  arrayFootprint W rationalWordWidth result.velocity+
    fields W [j,d,column.2,first.work,values.2,result.work,column.2+first.work,column.2+first.work+values.2,16*W]+256*W
def preparationProfile (model : RationalCostModel) (W j d R : ℕ) : ℕ := arrayProfile W d R+
  9*(natBits (preparationCap model W j d R)+W)+288*W

theorem point_bound {j d : ℕ} (model : RationalCostModel) (W C N H B R : ℕ) (betaN D : ℤ) (A : IntMatrix j)
    (rows : Rows j d) (initial : Vector d) (hBeta : betaN.natAbs≤B) (hD : D.natAbs≤H)
    (hA : ∀ i k,((A.read i).read k).natAbs≤H) (hc : ∀ i,(rows.read i).constant.natAbs≤C)
    (hs : ∀ i,(rows.read i).slope.natAbs≤C) (hr : ∀ i k,((rows.read i).coefficients.read k).natAbs≤C)
    (hi : ∀ i,(initial.read i).natAbs≤N) (hR : GeneralPaperBasisPreparationBits.pointWidth j d C N H B≤R)
    (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (hDim : binaryWordWidth (d+1)≤W) :
    pointWindow model W N betaN D A rows initial≤preparationProfile model W j d R := by
  let rhs := GeneralPaperBasisRHSBits.run model.rat W N betaN rows initial
  let first := GeneralPaperBasisSolveBits.run model.rat W N D A rhs.1
  let values := GeneralPaperBasisAssemblyBits.pointRun model.rat W N first.values initial
  let result := GeneralPaperBasisPreparationBits.point model.rat W N betaN D A rows initial
  have hRhs (i) : (rhs.1.read i).natAbs≤GeneralPaperBasisRHSBits.bound d C N B := by
    simp only [rhs,GeneralPaperBasisRHSBits.run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisRHSBits.scalar_bound model.rat W C N B betaN j (rows.read i) initial hBeta (hc i) (hs i) (hr i) hi
  have hSolveWidth := (GeneralPaperBasisPreparationBits.point_component_widths j d C N H B).2.1.trans hR
  have hPrefixWord := (GeneralPaperBasisSolveBits.component_widths j N H (GeneralPaperBasisRHSBits.bound d C N B)).2.trans hSolveWidth
  have hTailWord := (GeneralPaperBasisPreparationBits.point_component_widths j d C N H B).2.2.trans hR
  have hp (i) : rationalWordWidth (first.values.read i)≤R :=
    (rationalWordWidth_of_height (GeneralPaperBasisSolveBits.result_height model.rat W N H (GeneralPaperBasisRHSBits.bound d C N B) D A rhs.1 hD hA hRhs i)).trans hPrefixWord
  have hOutput := array_bound W R rationalWordWidth result.point (by
    intro k
    change rationalWordWidth ((GeneralPaperBasisAssemblyBits.pointRun model.rat W N first.values initial).1.read k)≤R
    rw [GeneralPaperBasisAssemblyBits.pointRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisAssemblyStorage.point_word model W N R first.values initial hp hi hTailWord k)
  have hWork := (GeneralPaperBasisPreparationBits.point_work model.rat model.monotone W C N H B hW hJ hDim betaN D A rows initial hBeta hD hA hc hs hr hi).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  change result.work≤preparationPrice model W j d R at hWork
  have hShape : result.work=rhs.2+first.work+values.2+16*W := rfl
  have hf := fields_bound W (natBits (preparationCap model W j d R))
    [j,d,rhs.2,first.work,values.2,result.work,rhs.2+first.work,rhs.2+first.work+values.2,16*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold preparationCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤9*(natBits (preparationCap model W j d R)+W)+32*W at hf
  unfold pointWindow preparationProfile
  dsimp only
  dsimp only [rhs,first,values,result] at hOutput hf
  omega

theorem direction_bound {j d : ℕ} (model : RationalCostModel) (W C H R : ℕ) (D : ℤ) (A : IntMatrix j)
    (rows : Rows j d) (next : Fin d) (hD : D.natAbs≤H) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hr : ∀ i k,((rows.read i).coefficients.read k).natAbs≤C) (hR : GeneralPaperBasisSolveBits.width j 1 H C≤R)
    (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (hDim : binaryWordWidth (d+1)≤W) :
    directionWindow model W D A rows next≤preparationProfile model W j d R := by
  let column := GeneralPaperBasisAssemblyBits.columnRun W rows next
  let first := GeneralPaperBasisSolveBits.run model.rat W 1 D A column.1
  let values := GeneralPaperBasisAssemblyBits.directionRun (d:=d) model.rat W first.values
  let result := GeneralPaperBasisPreparationBits.direction model.rat W D A rows next
  let s := GeneralPaperBasisDivideBits.height 1 H (j*H*C)
  have hColumn (i) : (column.1.read i).natAbs≤C := by
    rw [GeneralPaperBasisAssemblyBits.column_data,GeneralPaperBasisDirection.column_read]; exact hr i next
  have hp (i) : RationalHeight (first.values.read i) s := GeneralPaperBasisSolveBits.result_height model.rat W 1 H C D A column.1 hD hA hColumn i
  have hs : 1≤s := by have h := binaryWordWidth_pos 1; unfold s GeneralPaperBasisDivideBits.height; omega
  have hPrefixWord := (GeneralPaperBasisSolveBits.component_widths j 1 H C).2.trans hR
  have hOutput := array_bound W R rationalWordWidth result.velocity (by
    intro k
    change rationalWordWidth ((GeneralPaperBasisAssemblyBits.directionRun (d:=d) model.rat W first.values).1.read k)≤R
    rw [GeneralPaperBasisAssemblyBits.directionRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisAssemblyStorage.direction_word model W s R hs first.values hp hPrefixWord k)
  have hWork := (GeneralPaperBasisPreparationBits.direction_work model.rat model.monotone W C H hW hJ hDim D A rows next hD hA hr).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  change result.work≤preparationPrice model W j d R at hWork
  have hShape : result.work=column.2+first.work+values.2+16*W := rfl
  have hf := fields_bound W (natBits (preparationCap model W j d R))
    [j,d,column.2,first.work,values.2,result.work,column.2+first.work,column.2+first.work+values.2,16*W] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold preparationCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤9*(natBits (preparationCap model W j d R)+W)+32*W at hf
  unfold directionWindow preparationProfile
  dsimp only
  dsimp only [column,first,values,result] at hOutput hf
  omega

end Blotto.GeneralPaperBasisPreparationReturnStorage
