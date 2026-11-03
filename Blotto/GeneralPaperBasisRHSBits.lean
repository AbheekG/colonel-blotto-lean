import Blotto.GeneralPaperBasisCacheStageBits

/-! Actual fresh original-grid RHS with bit-priced tail dots and every
integer product/add/subtract/cast. No previous rational ray point enters
these computations. Intermediate values are bounded before cancellation.
-/
namespace Blotto.GeneralPaperBasisRHSBits
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisDenseRow
open GeneralPaperIntegerPrimitivePrice
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000

def bound (d C N B : ℕ) : ℕ := C*(N+B+d*N)
def coreCap (d C N B : ℕ) : ℕ := C+N+B+bound d C N B+1
def width (d C N B : ℕ) : ℕ :=
  1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap d C N)+binaryWordWidth (coreCap d C N B)

def scalar {d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (betaN : ℤ) (j : ℕ) (row : Dense d) (initial : Vector d) : ℤ × ℕ :=
  let dot := GeneralPaperIntegerDotPrice.run primitive W row.coefficients.read (tailVector j initial)
  let a := (N:ℤ)*row.constant
  let b := betaN*row.slope
  (a+b-dot.value,dot.work+32*W+primitive (word (N:ℤ))+
    binary primitive (fun x y => x*y) (N:ℤ) row.constant+
    binary primitive (fun x y => x*y) betaN row.slope+
    binary primitive (fun x y => x+y) a b+binary primitive (fun x y => x-y) (a+b) dot.value)

theorem scalar_data {d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (betaN : ℤ) (j : ℕ) (row : Dense d) (initial : Vector d) :
    (scalar primitive W N betaN j row initial).1=(N:ℤ)*row.constant+betaN*row.slope-
      (GeneralPaperBasisIntegerDot.run row.coefficients.read (tailVector j initial)).value := by
  simp only [scalar,GeneralPaperIntegerDotPrice.data]

theorem tail_bound {d : ℕ} (j N : ℕ) (initial : Vector d) (hGrid : ∀ i,(initial.read i).natAbs≤N) (i : Fin d) :
    (tailVector j initial i).natAbs≤N := by
  by_cases hi : j ≤ i.val
  · simpa only [tailVector,hi,ite_true] using hGrid i
  · simp only [tailVector,hi,ite_false,Int.natAbs_zero]; exact Nat.zero_le _

theorem scalar_work {d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W C N B : ℕ) (betaN : ℤ)
    (j : ℕ) (row : Dense d) (initial : Vector d) (hBeta : betaN.natAbs≤B)
    (hConstant : row.constant.natAbs≤C) (hSlope : row.slope.natAbs≤C)
    (hRow : ∀ i,(row.coefficients.read i).natAbs≤C) (hGrid : ∀ i,(initial.read i).natAbs≤N) :
    (scalar primitive W N betaN j row initial).2≤512*(d+1)*(W+primitive (width d C N B)) := by
  let M := coreCap d C N B
  let Q := primitive (width d C N B)
  let dot := GeneralPaperIntegerDotPrice.run primitive W row.coefficients.read (tailVector j initial)
  have hDot : dot.value.natAbs≤d*C*N := by
    rw [GeneralPaperIntegerDotPrice.data]
    exact GeneralPaperIntegerDotSize.run_bound _ _ C N hRow (tail_bound j N initial hGrid)
  have hA : ((N:ℤ)*row.constant).natAbs≤N*C := by rw [Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.mul_le_mul_left N hConstant
  have hB : (betaN*row.slope).natAbs≤B*C := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul hBeta hSlope
  have hSum := (Int.natAbs_add_le ((N:ℤ)*row.constant) (betaN*row.slope)).trans (Nat.add_le_add hA hB)
  have hSub := (Int.natAbs_sub_le ((N:ℤ)*row.constant+betaN*row.slope) dot.value).trans (Nat.add_le_add hSum hDot)
  have hMass : N*C+B*C+d*C*N=bound d C N B := by unfold bound; ring
  have hInputs : C≤M ∧ N≤M ∧ B≤M ∧ bound d C N B≤M := by dsimp only [M,coreCap]; omega
  have hAm : ((N:ℤ)*row.constant).natAbs≤M := by omega
  have hBm : (betaN*row.slope).natAbs≤M := by omega
  have hSm : ((N:ℤ)*row.constant+betaN*row.slope).natAbs≤M := by omega
  have hDm : dot.value.natAbs≤M := by omega
  have hTm : ((N:ℤ)*row.constant+betaN*row.slope-dot.value).natAbs≤M := by omega
  have hCast := hMono (word_bound (N:ℤ) M (by simpa only [Int.natAbs_natCast] using hInputs.2.1))
  have hP := binary_le primitive hMono (fun x y => x*y) (N:ℤ) row.constant M
    (by simpa only [Int.natAbs_natCast] using hInputs.2.1) (hConstant.trans hInputs.1) hAm
  have hQ := binary_le primitive hMono (fun x y => x*y) betaN row.slope M
    (hBeta.trans hInputs.2.2.1) (hSlope.trans hInputs.1) hBm
  have hS := binary_le primitive hMono (fun x y => x+y) _ _ M hAm hBm hSm
  have hT := binary_le primitive hMono (fun x y => x-y) _ _ M hSm hDm hTm
  have hPromote : primitive (1+binaryWordWidth M)≤Q := by apply hMono; dsimp only [M,width]; omega
  have hLoop := (GeneralPaperIntegerDotPrice.work primitive hMono W C N row.coefficients.read (tailVector j initial)
    hRow (tail_bound j N initial hGrid)).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono (show 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap d C N)≤width d C N B by unfold width; omega)) W))
  change dot.work≤128*(d+1)*(W+Q) at hLoop
  change dot.work+32*W+primitive (word (N:ℤ))+binary primitive (fun x y => x*y) (N:ℤ) row.constant+
    binary primitive (fun x y => x*y) betaN row.slope+binary primitive (fun x y => x+y) _ _+
    binary primitive (fun x y => x-y) _ dot.value≤512*(d+1)*(W+Q)
  nlinarith only [hCast,hP,hQ,hS,hT,hPromote,hLoop,Nat.zero_le (d*W),Nat.zero_le (d*Q)]

theorem scalar_bound {d : ℕ} (primitive : ℕ → ℕ) (W C N B : ℕ) (betaN : ℤ) (j : ℕ) (row : Dense d) (initial : Vector d)
    (hBeta : betaN.natAbs≤B) (hConstant : row.constant.natAbs≤C) (hSlope : row.slope.natAbs≤C)
    (hRow : ∀ i,(row.coefficients.read i).natAbs≤C) (hGrid : ∀ i,(initial.read i).natAbs≤N) :
    (scalar primitive W N betaN j row initial).1.natAbs≤bound d C N B := by
  rw [scalar_data]
  have hd := GeneralPaperIntegerDotSize.run_bound row.coefficients.read (tailVector j initial) C N hRow (tail_bound j N initial hGrid)
  have ha : ((N:ℤ)*row.constant).natAbs≤N*C := by rw [Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.mul_le_mul_left N hConstant
  have hb : (betaN*row.slope).natAbs≤B*C := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul hBeta hSlope
  have hs := (Int.natAbs_add_le ((N:ℤ)*row.constant) (betaN*row.slope)).trans (Nat.add_le_add ha hb)
  have ht := (Int.natAbs_sub_le ((N:ℤ)*row.constant+betaN*row.slope)
    (GeneralPaperBasisIntegerDot.run row.coefficients.read (tailVector j initial)).value).trans (Nat.add_le_add hs hd)
  unfold bound
  nlinarith only [ht]

def run {j d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) : Vector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (fun i => scalar primitive W N betaN j (rows.read i) initial)

theorem data {j d : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (betaN : ℤ) (rows : Rows j d) (initial : Vector d) :
    (run primitive W N betaN rows initial).1=(GeneralPaperBasisFreshRHS.rhsRun N betaN rows initial).1 := by
  simp only [run,GeneralPaperBasisFreshRHS.rhsRun,PaperIndexedArrayConstruction.run_data,scalar_data]

theorem work {j d : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W C N B : ℕ)
    (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (betaN : ℤ) (rows : Rows j d) (initial : Vector d)
    (hBeta : betaN.natAbs≤B) (hConstant : ∀ i,(rows.read i).constant.natAbs≤C)
    (hSlope : ∀ i,(rows.read i).slope.natAbs≤C) (hRow : ∀ i k,((rows.read i).coefficients.read k).natAbs≤C)
    (hGrid : ∀ i,(initial.read i).natAbs≤N) :
    (run primitive W N betaN rows initial).2≤1024*(j+1)*(d+1)*(W+primitive (width d C N B)) := by
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => scalar_work primitive hMono W C N B betaN j (rows.read i) initial hBeta
    (hConstant i) (hSlope i) (hRow i) hGrid)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun i : Fin j => scalar primitive W N betaN j (rows.read i) initial)
  change (run primitive W N betaN rows initial).2≤_ at hh
  have hO : 6*W+10*1*binaryWordWidth (j+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (j+1) hO
  nlinarith only [hs,hh,ho,Nat.zero_le (j*d*W),Nat.zero_le (d*W),Nat.zero_le (j*W),
    Nat.zero_le (j*d*primitive (width d C N B)),Nat.zero_le (j*primitive (width d C N B)),
    Nat.zero_le (d*primitive (width d C N B)),Nat.zero_le (primitive (width d C N B))]

end Blotto.GeneralPaperBasisRHSBits
