import Blotto.GeneralPaperParametricRunWork

/-! Materialize the actual affine input fields from the reused score matrix
and two stored ray-anchor readers. This writes coefficient/score references,
not copies of rational payloads. Unit and bit index profiles share the data.
-/
namespace Blotto.GeneralPaperAffineInputPrice
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayAffineScoreStep
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

def fieldRun {m K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (j : Fin m) : Field K × ℕ :=
  PaperIndexedArrayConstruction.run indexPrimitive W (fun l =>
    ((GeneralPaperRayQueryWork.scores matrix j l,
      Affine.mk (GeneralPaperRayAnchorCosts.anchorQ x j l) (GeneralPaperRayAnchorCosts.anchorQ w j l)),64*W))

theorem field_data {m K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) (j : Fin m) :
    (fieldRun indexPrimitive W matrix x w j).1=FixedArrayTable.ofFn (fun l =>
      (GeneralPaperRayQueryWork.scores matrix j l,
        Affine.mk (GeneralPaperRayAnchorCosts.anchorQ x j l) (GeneralPaperRayAnchorCosts.anchorQ w j l))) := by
  exact PaperIndexedArrayConstruction.run_data _ _ _

theorem field_bit_work {m K : ℕ} (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (j : Fin m) (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) :
    (fieldRun (fun w => w) W matrix x w j).2≤128*(K+1)*W := by
  have ha := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W (fun l =>
    ((GeneralPaperRayQueryWork.scores matrix j l,
      Affine.mk (GeneralPaperRayAnchorCosts.anchorQ x j l) (GeneralPaperRayAnchorCosts.anchorQ w j l)),64*W))
  change (fieldRun (fun w => w) W matrix x w j).2≤_ at ha
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at ha
  have hp : 6*W+10*binaryWordWidth (K+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (K+1) hp
  nlinarith only [ha,ho]

theorem field_arithmetic_work {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (j : Fin m) :
    (fieldRun (fun _ => 1) 1 matrix x w j).2≤128*(K+1) := by
  have ha := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (fun l =>
    ((GeneralPaperRayQueryWork.scores matrix j l,
      Affine.mk (GeneralPaperRayAnchorCosts.anchorQ x j l) (GeneralPaperRayAnchorCosts.anchorQ w j l)),64*1))
  change (fieldRun (fun _ => 1) 1 matrix x w j).2=_ at ha
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at ha
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 K K
  nlinarith only [ha,ho]

def matrixRun {m K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) : FixedArrayTable m (Field K) × ℕ :=
  PaperIndexedArrayConstruction.run indexPrimitive W (fieldRun indexPrimitive W matrix x w)

theorem matrix_data {m K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) :
    (matrixRun indexPrimitive W matrix x w).1=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun l =>
      (GeneralPaperRayQueryWork.scores matrix j l,
        Affine.mk (GeneralPaperRayAnchorCosts.anchorQ x j l) (GeneralPaperRayAnchorCosts.anchorQ w j l)))) := by
  simp only [matrixRun,PaperIndexedArrayConstruction.run_data,field_data]

theorem matrix_bit_work {m K : ℕ} (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    (matrixRun (fun w => w) W matrix x w).2≤256*(m+1)*(K+1)*W := by
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => field_bit_work W matrix x w j hW hK)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have ha := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fieldRun (fun w => w) W matrix x w)
  change (matrixRun (fun w => w) W matrix x w).2≤_ at ha
  have hp : 6*W+10*binaryWordWidth (m+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (m+1) hp
  have hc : (m+1)*W≤(m+1)*(K+1)*W := by nlinarith only [Nat.zero_le ((m+1)*K*W)]
  nlinarith only [ha,hs,ho,hc,Nat.zero_le ((K+1)*W)]

theorem matrix_arithmetic_work {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) : (matrixRun (fun _ => 1) 1 matrix x w).2≤256*(m+1)*(K+1) := by
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => field_arithmetic_work matrix x w j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have ha := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (fieldRun (fun _ => 1) 1 matrix x w)
  change (matrixRun (fun _ => 1) 1 matrix x w).2=_ at ha
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 m m
  nlinarith only [ha,hs,ho]

def run {m K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) : List (Field K) × ℕ :=
  let result := matrixRun indexPrimitive W matrix x w
  (result.1.data.toList,result.2+(8*m+4)*W)

theorem data {m K : ℕ} (indexPrimitive : ℕ → ℕ) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ) :
    (run indexPrimitive W matrix x w).1=GeneralPaperRayAffineScoreInput.fields matrix x w := by
  simp only [run,matrix_data,FixedArrayTable.ofFn,Array.toList_ofFn,GeneralPaperRayAffineScoreInput.fields]

theorem bit_work {m K : ℕ} (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    (run (fun w => w) W matrix x w).2≤512*(m+1)*(K+1)*W := by
  have hm := matrix_bit_work W matrix x w hW hK hM
  have hc : (m+1)*W≤(m+1)*(K+1)*W := by nlinarith only [Nat.zero_le ((m+1)*K*W)]
  change (matrixRun (fun w => w) W matrix x w).2+(8*m+4)*W≤_
  nlinarith only [hm,hc]

theorem arithmetic_work {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) : (run (fun _ => 1) 1 matrix x w).2≤512*(m+1)*(K+1) := by
  have hm := matrix_arithmetic_work matrix x w
  change (matrixRun (fun _ => 1) 1 matrix x w).2+(8*m+4)*1≤_
  nlinarith only [hm]

end Blotto.GeneralPaperAffineInputPrice
