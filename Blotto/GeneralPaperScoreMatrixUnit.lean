import Blotto.GeneralPaperBasisDenseWork

/-! Prepare the actual score matrix once with unit index operations at
both array levels. Floor-score arguments, anchors and scores are identical
to the native preparation reused by every basis and ray stage.
-/
namespace Blotto.GeneralPaperScoreMatrixUnit
open RationalOrderCell GeneralPaperDictionary GeneralPaperExactScoreDP
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

def fieldRun {T m K : ℕ} (depth : ℕ) (dict : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) : Field K × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun l =>
    let score := GeneralPaperScoreMatrixWork.scoreRun depth v S j l
    ((score.1,dict.anchor j l),score.2+4))

theorem field_data {T m K : ℕ} (depth : ℕ) (dict : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) :
    (fieldRun depth dict v S j).1=(GeneralPaperScoreMatrixWork.fieldRun depth dict v S j).1 := by
  simp only [fieldRun,GeneralPaperScoreMatrixWork.fieldRun,PaperIndexedArrayConstruction.run_data]

theorem field_work {T m K : ℕ} (depth : ℕ) (dict : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) :
    (fieldRun depth dict v S j).2≤128*(K+1)*(depth+1) := by
  have hh := GeneralPaperUnitArrayReprice.work 1 (fun l : Fin K =>
    (((GeneralPaperScoreMatrixWork.scoreRun depth v S j l).1,dict.anchor j l),
      (GeneralPaperScoreMatrixWork.scoreRun depth v S j l).2+4))
  change (fieldRun depth dict v S j).2=(GeneralPaperScoreMatrixWork.fieldRun depth dict v S j).2+8*K+2 at hh
  have ho := GeneralPaperScoreMatrixWork.field_work depth dict v S j
  nlinarith only [hh,ho,Nat.zero_le (K*depth)]

def run {T m K : ℕ} (depth : ℕ) (dict : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) : FixedArrayTable m (Field K) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fieldRun depth dict v S)

theorem data {T m K : ℕ} (depth : ℕ) (dict : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) :
    (run depth dict v S).1=(GeneralPaperScoreMatrixWork.matrixRun depth dict v S).1 := by
  simp only [run,GeneralPaperScoreMatrixWork.matrixRun,PaperIndexedArrayConstruction.run_data,field_data]

theorem work {T m K : ℕ} (depth : ℕ) (dict : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) :
    (run depth dict v S).2≤256*(m+1)*(K+1)*(depth+1) := by
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => field_work depth dict v S j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (fieldRun depth dict v S)
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 m m
  change (run depth dict v S).2=_ at hh
  have hp : 1≤(K+1)*(depth+1) := Nat.mul_pos (by omega) (by omega)
  have hc := Nat.mul_le_mul_left (m+1) hp
  nlinarith only [hs,hh,ho,hc]

end Blotto.GeneralPaperScoreMatrixUnit
