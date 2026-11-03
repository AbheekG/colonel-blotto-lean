import Blotto.GeneralPaperBasisAssemblyBits

/-! Complete bit-priced fresh point/direction preparation. RHS magnitudes
and prefix heights are derived from the actual operations, not supplied
as phase/shape/size oracles. Every returned array is literal native data.
-/
namespace Blotto.GeneralPaperBasisPreparationBits
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def pointWidth (j d C N H B : ℕ) : ℕ := 1+GeneralPaperBasisRHSBits.width d C N B+
  GeneralPaperBasisSolveBits.width j N H (GeneralPaperBasisRHSBits.bound d C N B)+4*binaryWordWidth N

theorem point_component_widths (j d C N H B : ℕ) :
    GeneralPaperBasisRHSBits.width d C N B≤pointWidth j d C N H B ∧
    GeneralPaperBasisSolveBits.width j N H (GeneralPaperBasisRHSBits.bound d C N B)≤pointWidth j d C N H B ∧
    1+4*binaryWordWidth N≤pointWidth j d C N H B := by unfold pointWidth; omega

def point {j d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) : GeneralPaperBasisFreshPoint.Result d :=
  let rhs := GeneralPaperBasisRHSBits.run primitive W N betaN rows initial
  let first := GeneralPaperBasisSolveBits.run primitive W N D A rhs.1
  let values := GeneralPaperBasisAssemblyBits.pointRun primitive W N first.values initial
  ⟨values.1,rhs.2+first.work+values.2+16*W⟩

theorem point_data {j d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d) :
    (point primitive W N betaN D A rows initial).point=(GeneralPaperBasisFreshPoint.run N betaN D A rows initial).point := by
  simp only [point,GeneralPaperBasisFreshPoint.run,GeneralPaperBasisRHSBits.data,GeneralPaperBasisSolveBits.data,GeneralPaperBasisAssemblyBits.point_data]

theorem point_work {j d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W C N H B : ℕ)
    (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (hDim : binaryWordWidth (d+1)≤W)
    (betaN D : ℤ) (A : IntMatrix j) (rows : Rows j d) (initial : Vector d)
    (hBeta : betaN.natAbs≤B) (hD : D.natAbs≤H) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hConstant : ∀ i,(rows.read i).constant.natAbs≤C) (hSlope : ∀ i,(rows.read i).slope.natAbs≤C)
    (hRow : ∀ i k,((rows.read i).coefficients.read k).natAbs≤C) (hGrid : ∀ i,(initial.read i).natAbs≤N) :
    (point primitive W N betaN D A rows initial).work≤4096*(j+1)*(j+d+2)*(W+primitive (pointWidth j d C N H B)) := by
  let R := GeneralPaperBasisRHSBits.bound d C N B
  let Q := primitive (pointWidth j d C N H B)
  let rhs := GeneralPaperBasisRHSBits.run primitive W N betaN rows initial
  let first := GeneralPaperBasisSolveBits.run primitive W N D A rhs.1
  let values := GeneralPaperBasisAssemblyBits.pointRun primitive W N first.values initial
  have hr (i) : (rhs.1.read i).natAbs≤R := by
    simp only [rhs,GeneralPaperBasisRHSBits.run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperBasisRHSBits.scalar_bound primitive W C N B betaN j (rows.read i) initial hBeta
      (hConstant i) (hSlope i) (hRow i) hGrid
  have hw := point_component_widths j d C N H B
  have hRhs := (GeneralPaperBasisRHSBits.work primitive hMono W C N B hW hJ betaN rows initial
    hBeta hConstant hSlope hRow hGrid).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.1) W))
  have hFirst := (GeneralPaperBasisSolveBits.work primitive hMono W N H R hW hJ D A rhs.1 hD hA hr).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.2.1) W))
  have hValues := (GeneralPaperBasisAssemblyBits.point_work primitive hMono W N hW hDim first.values initial hGrid).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.2.2) W))
  change rhs.2≤1024*(j+1)*(d+1)*(W+Q) at hRhs
  change first.work≤1024*(j+1)^2*(W+Q) at hFirst
  change values.2≤128*(d+1)*(W+Q) at hValues
  change rhs.2+first.work+values.2+16*W≤4096*(j+1)*(j+d+2)*(W+Q)
  nlinarith only [hRhs,hFirst,hValues,Nat.zero_le (j*j*W),Nat.zero_le (j*d*W),Nat.zero_le (j*W),Nat.zero_le (d*W),
    Nat.zero_le (j*j*Q),Nat.zero_le (j*d*Q),Nat.zero_le (j*Q),Nat.zero_le (d*Q),Nat.zero_le Q]

def direction {j d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) : GeneralPaperBasisDirection.Result d :=
  let column := GeneralPaperBasisAssemblyBits.columnRun W rows next
  let first := GeneralPaperBasisSolveBits.run primitive W 1 D A column.1
  let values := GeneralPaperBasisAssemblyBits.directionRun primitive W first.values
  ⟨values.1,column.2+first.work+values.2+16*W⟩

theorem direction_data {j d : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d) :
    (direction primitive W D A rows next).velocity=(GeneralPaperBasisDirection.run D A rows next).velocity := by
  simp only [direction,GeneralPaperBasisDirection.run,GeneralPaperBasisAssemblyBits.column_data,GeneralPaperBasisSolveBits.data,GeneralPaperBasisAssemblyBits.direction_data]

theorem direction_work {j d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W C H : ℕ)
    (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (hDim : binaryWordWidth (d+1)≤W)
    (D : ℤ) (A : IntMatrix j) (rows : Rows j d) (next : Fin d)
    (hD : D.natAbs≤H) (hA : ∀ i k,((A.read i).read k).natAbs≤H) (hRow : ∀ i k,((rows.read i).coefficients.read k).natAbs≤C) :
    (direction primitive W D A rows next).work≤4096*(j+1)*(j+d+2)*(W+primitive (GeneralPaperBasisSolveBits.width j 1 H C)) := by
  let Q := primitive (GeneralPaperBasisSolveBits.width j 1 H C)
  let column := GeneralPaperBasisAssemblyBits.columnRun W rows next
  let first := GeneralPaperBasisSolveBits.run primitive W 1 D A column.1
  let values := GeneralPaperBasisAssemblyBits.directionRun (d:=d) primitive W first.values
  let s := GeneralPaperBasisDivideBits.height 1 H (j*H*C)
  have hCol (i) : (column.1.read i).natAbs≤C := by
    rw [GeneralPaperBasisAssemblyBits.column_data,GeneralPaperBasisDirection.column_read]
    exact hRow i next
  have hf (i) : RationalHeight (first.values.read i) s := GeneralPaperBasisSolveBits.result_height primitive W 1 H C D A column.1 hD hA hCol i
  have hs : 1≤s := by
    have hh := binaryWordWidth_pos 1
    dsimp only [s,GeneralPaperBasisDivideBits.height]
    omega
  have hw := (GeneralPaperBasisSolveBits.component_widths j 1 H C).2
  have hColumn := GeneralPaperBasisAssemblyBits.column_work W hW hJ rows next
  have hFirst := GeneralPaperBasisSolveBits.work primitive hMono W 1 H C hW hJ D A column.1 hD hA hCol
  have hValues := (GeneralPaperBasisAssemblyBits.direction_work primitive hMono W s hW hDim hs first.values hf).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw) W))
  change first.work≤1024*(j+1)^2*(W+Q) at hFirst
  change values.2≤128*(d+1)*(W+Q) at hValues
  change column.2≤64*(j+1)*W at hColumn
  change column.2+first.work+values.2+16*W≤4096*(j+1)*(j+d+2)*(W+Q)
  nlinarith only [hColumn,hFirst,hValues,Nat.zero_le (j*j*W),Nat.zero_le (j*d*W),Nat.zero_le (j*W),Nat.zero_le (d*W),
    Nat.zero_le (j*j*Q),Nat.zero_le (j*d*Q),Nat.zero_le (j*Q),Nat.zero_le (d*Q),Nat.zero_le Q]

end Blotto.GeneralPaperBasisPreparationBits
