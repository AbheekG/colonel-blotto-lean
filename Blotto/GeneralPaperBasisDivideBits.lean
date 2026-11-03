import Blotto.GeneralPaperBasisRHSBits

/-! Fresh rational prefix division using the literal N*D denominator.
Casts, denominator multiplication, division and result writes all use
their actual rational operand widths; no cancellation assumption is used.
-/
namespace Blotto.GeneralPaperBasisDivideBits
open GeneralPaperBasisStoredProducts GeneralPaperRationalPrimitivePrice
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000

def height (N H U : ℕ) : ℕ := binaryWordWidth N+binaryWordWidth H+binaryWordWidth U

theorem nat_height (N : ℕ) : RationalHeight (N:ℚ) (binaryWordWidth N) := by
  simpa only [Int.cast_natCast] using GeneralPaperBasisStageSize.int_height (N:ℤ) N (by simp only [Int.natAbs_natCast,le_refl])

theorem heights (N H U : ℕ) (D numerator : ℤ) (hD : D.natAbs≤H) (hU : numerator.natAbs≤U) :
    RationalHeight (N:ℚ) (height N H U) ∧ RationalHeight (D:ℚ) (height N H U) ∧
    RationalHeight (numerator:ℚ) (height N H U) ∧ RationalHeight ((N:ℚ)*(D:ℚ)) (height N H U) ∧
    RationalHeight ((numerator:ℚ)/((N:ℚ)*(D:ℚ))) (height N H U) := by
  have hn := nat_height N
  have hd := GeneralPaperBasisStageSize.int_height D H hD
  have hu := GeneralPaperBasisStageSize.int_height numerator U hU
  have hp := hn.mul hd
  have hv := hu.div hp
  exact ⟨hn.mono (by unfold height; omega),hd.mono (by unfold height; omega),hu.mono (by unfold height; omega),
    hp.mono (by unfold height; omega),hv.mono (by unfold height; omega)⟩

def scalar (primitive : ℕ → ℕ) (W N : ℕ) (D numerator : ℤ) : ℚ × ℕ :=
  let denominator := (N:ℚ)*(D:ℚ)
  ((numerator:ℚ)/denominator,32*W+primitive (rationalWordWidth (N:ℚ))+primitive (rationalWordWidth (D:ℚ))+
    primitive (rationalWordWidth (numerator:ℚ))+binary primitive (fun a b => a*b) (N:ℚ) (D:ℚ)+
    binary primitive (fun a b => a/b) (numerator:ℚ) denominator)

theorem scalar_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W N H U : ℕ)
    (D numerator : ℤ) (hD : D.natAbs≤H) (hU : numerator.natAbs≤U) :
    (scalar primitive W N D numerator).2≤32*W+7*primitive (1+2*height N H U) := by
  have hh := heights N H U D numerator hD hU
  have hN := rationalWordWidth_of_height hh.1
  have hD' := rationalWordWidth_of_height hh.2.1
  have hU' := rationalWordWidth_of_height hh.2.2.1
  have hP := rationalWordWidth_of_height hh.2.2.2.1
  have hV := rationalWordWidth_of_height hh.2.2.2.2
  have hn := hMono hN
  have hd := hMono hD'
  have hu := hMono hU'
  have hp := binary_le primitive hMono (fun a b => a*b) (N:ℚ) (D:ℚ) _ hN hD' hP
  have hv := binary_le primitive hMono (fun a b => a/b) (numerator:ℚ) ((N:ℚ)*(D:ℚ)) _ hU' hP hV
  dsimp only [scalar]
  omega

def run {j : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (D : ℤ) (numerators : Vector j) : GeneralPaperBasisRationalSolve.RatVector j × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (fun i => scalar primitive W N D (numerators.read i))

theorem data {j : ℕ} (primitive : ℕ → ℕ) (W N : ℕ) (D : ℤ) (numerators : Vector j) :
    (run primitive W N D numerators).1=(GeneralPaperBasisRationalSolve.divideRun N D numerators).1 := by
  simp only [run,scalar,GeneralPaperBasisRationalSolve.divideRun,PaperIndexedArrayConstruction.run_data]

theorem work {j : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W N H U : ℕ)
    (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (D : ℤ) (numerators : Vector j)
    (hD : D.natAbs≤H) (hU : ∀ i,(numerators.read i).natAbs≤U) :
    (run primitive W N D numerators).2≤128*(j+1)*(W+primitive (1+2*height N H U)) := by
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => scalar_work primitive hMono W N H U D (numerators.read i) hD (hU i))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun i : Fin j => scalar primitive W N D (numerators.read i))
  change (run primitive W N D numerators).2≤_ at hh
  have hO : 6*W+10*1*binaryWordWidth (j+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (j+1) hO
  nlinarith only [hs,hh,ho,Nat.zero_le (j*W),Nat.zero_le (j*primitive (1+2*height N H U))]

end Blotto.GeneralPaperBasisDivideBits
