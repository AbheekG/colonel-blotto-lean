import Blotto.GeneralPaperBasisDivideBits

/-! Complete fresh rational prefix solve: one stored integer adjugate
product and literal N*D division per coordinate. Bit prices cover raw
dot/cast/multiply/divide operands; returned values are exactly native data.
-/
namespace Blotto.GeneralPaperBasisSolveBits
open GeneralPaperBasisStoredProducts
set_option autoImplicit false
set_option maxHeartbeats 7000000

def width (j N H R : ℕ) : ℕ := 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap j H R)+
  2*GeneralPaperBasisDivideBits.height N H (j*H*R)

theorem component_widths (j N H R : ℕ) :
    1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap j H R)≤width j N H R ∧
    1+2*GeneralPaperBasisDivideBits.height N H (j*H*R)≤width j N H R := by unfold width; omega

def run {j : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) : GeneralPaperBasisRationalSolve.Result j :=
  let numerators := GeneralPaperBasisProductBits.mulVecRun primitive W A rhs
  let values := GeneralPaperBasisDivideBits.run primitive W N D numerators.1
  ⟨values.1,numerators.2+values.2+8*W⟩

theorem data {j : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j) :
    (run primitive W N D A rhs).values=(GeneralPaperBasisRationalSolve.run N D A rhs).values := by
  simp only [run,GeneralPaperBasisRationalSolve.run,GeneralPaperBasisProductBits.mulVec_data,GeneralPaperBasisDivideBits.data]

theorem result_height {j : ℕ} (primitive : ℕ → ℕ) (W N H R : ℕ) (D : ℤ) (A : IntMatrix j) (rhs : Vector j)
    (hD : D.natAbs≤H) (hA : ∀ i k,((A.read i).read k).natAbs≤H) (hr : ∀ i,(rhs.read i).natAbs≤R) (i : Fin j) :
    RationalHeight ((run primitive W N D A rhs).values.read i) (GeneralPaperBasisDivideBits.height N H (j*H*R)) := by
  rw [data,GeneralPaperBasisRationalSolve.read]
  have hh := GeneralPaperStoredProductSize.mulVec A rhs H R hA hr i
  rw [GeneralPaperBasisStoredProducts.mulVec_data] at hh
  exact (GeneralPaperBasisDivideBits.heights N H (j*H*R) D _ hD hh).2.2.2.2

theorem work {j : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W N H R : ℕ)
    (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (D : ℤ) (A : IntMatrix j) (rhs : Vector j)
    (hD : D.natAbs≤H) (hA : ∀ i k,((A.read i).read k).natAbs≤H) (hr : ∀ i,(rhs.read i).natAbs≤R) :
    (run primitive W N D A rhs).work≤1024*(j+1)^2*(W+primitive (width j N H R)) := by
  let Q := primitive (width j N H R)
  let numerators := GeneralPaperBasisProductBits.mulVecRun primitive W A rhs
  have hNum (i) : (numerators.1.read i).natAbs≤j*H*R := by
    rw [GeneralPaperBasisProductBits.mulVec_data]
    exact GeneralPaperStoredProductSize.mulVec A rhs H R hA hr i
  have hw := component_widths j N H R
  have hm := (GeneralPaperBasisProductBits.mulVec_work primitive hMono W H R hW hJ A rhs hA hr).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.1) W))
  have hd := (GeneralPaperBasisDivideBits.work primitive hMono W N H (j*H*R) hW hJ D numerators.1 hD hNum).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono hw.2) W))
  change numerators.2≤512*(j+1)^2*(W+Q) at hm
  change _≤128*(j+1)*(W+Q) at hd
  change numerators.2+(GeneralPaperBasisDivideBits.run primitive W N D numerators.1).2+8*W≤1024*(j+1)^2*(W+Q)
  nlinarith only [hm,hd,Nat.zero_le (j*W),Nat.zero_le (j*Q)]

theorem width_bound (j N H R : ℕ) : width j N H R≤
    16*(binaryWordWidth (j+1)+binaryWordWidth (N+1)+binaryWordWidth (H+1)+binaryWordWidth (R+1)+1) := by
  have hc := GeneralPaperIntegerDotPrice.cap_width j H R
  have h1 := binaryWordWidth_mul (j*H) R
  have h2 := binaryWordWidth_mul j H
  have hj : binaryWordWidth j≤binaryWordWidth (j+1) := binaryWordWidth_mono (by omega)
  have hn : binaryWordWidth N≤binaryWordWidth (N+1) := binaryWordWidth_mono (by omega)
  have hh : binaryWordWidth H≤binaryWordWidth (H+1) := binaryWordWidth_mono (by omega)
  have hr : binaryWordWidth R≤binaryWordWidth (R+1) := binaryWordWidth_mono (by omega)
  unfold width GeneralPaperBasisDivideBits.height
  omega

end Blotto.GeneralPaperBasisSolveBits
