import Blotto.GeneralPaperRayBracket

/-! Fixed-point feasibility-query arithmetic profile. Scores are read from
the already materialized score matrix and reused. Indexed construction
materializes each ray cost once; one stored complete DP and one score scan
produce the high minimum. These are paper source-model operation counts;
fast-bit prices and simultaneous abstract space are separate joins.
-/
namespace Blotto.GeneralPaperRayQueryWork
open RationalOrderCell GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperRayAnchorCosts
set_option autoImplicit false
set_option maxHeartbeats 2500000

def scores {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (j : Fin m) (l : Fin K) : ℕ :=
  ((matrix.read j).read l).1

def fieldRun {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) (j : Fin m) : Field K × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun l => ((scores matrix j l,costs x w t j l),24))

theorem field_data {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) (j : Fin m) :
    (fieldRun matrix x w t j).1=FixedArrayTable.ofFn (fun l => (scores matrix j l,costs x w t j l)) := by
  exact PaperIndexedArrayConstruction.run_data _ _ _

theorem field_work {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) (j : Fin m) :
    (fieldRun matrix x w t j).2≤128*(K+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun l => ((scores matrix j l,costs x w t j l),24))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul] at hh
  change (fieldRun matrix x w t j).2≤K*24+(K+1)*(6+10*0*binaryWordWidth (K+1)+28) at hh
  norm_num only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.reduceAdd] at hh
  omega

def matrixRun {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) : FixedArrayTable m (Field K) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fieldRun matrix x w t)

theorem matrix_data {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) :
    (matrixRun matrix x w t).1=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun l => (scores matrix j l,costs x w t j l))) := by
  simp only [matrixRun,PaperIndexedArrayConstruction.run_data,field_data]

theorem matrix_work {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) :
    (matrixRun matrix x w t).2≤256*(m+1)*(K+1) := by
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => field_work matrix x w t j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1 (fieldRun matrix x w t)
  change (matrixRun matrix x w t).2≤_ at hh
  simp only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  nlinarith only [hs,hh]

def fieldsRun {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) : List (Field K) × ℕ :=
  let r := matrixRun matrix x w t
  (r.1.data.toList,r.2+8*m+4)

theorem fields_data {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) :
    (fieldsRun matrix x w t).1=fields (scores matrix) (costs x w t) := by
  simp only [fieldsRun,matrix_data,FixedArrayTable.ofFn,Array.toList_ofFn,fields]

theorem fields_work {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) :
    (fieldsRun matrix x w t).2≤512*(m+1)*(K+1) := by
  have hh := matrix_work matrix x w t
  change (matrixRun matrix x w t).2+8*m+4≤_
  nlinarith only [hh]

def minimumRun {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) (S h : ℕ) : Option (Selection K) × ℕ :=
  let inputs := fieldsRun matrix x w t
  let table := GeneralPaperScoreDPWork.runWithWork S inputs.1
  let selected := GeneralPaperScoreDPWork.scanRun (fun s => (GeneralPaperRayHighMinimum.candidate table.1 h s,12)) (List.finRange (S+1))
  (selected.1,inputs.2+table.2+selected.2+4*(S+1)+8)

theorem minimum_data {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) (S h : ℕ) :
    (minimumRun matrix x w t S h).1=GeneralPaperRayHighMinimum.minimum (scores matrix) (costs x w t) S h := by
  simp only [minimumRun,GeneralPaperScoreDPWork.scan_data,GeneralPaperScoreDPWork.run_data,fields_data,
    GeneralPaperRayHighMinimum.minimum]

theorem minimum_work {m K : ℕ} (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ) (t : ℚ) (S h : ℕ) :
    (minimumRun matrix x w t S h).2≤1024*(m+1)*(K+1)*(S+1) := by
  have hf := fields_work matrix x w t
  have hd := GeneralPaperScoreDPWork.run_work S (fieldsRun matrix x w t).1
  rw [fields_data] at hd
  simp only [fields,List.length_ofFn] at hd
  change (GeneralPaperScoreDPWork.runWithWork S (fields (scores matrix) (costs x w t))).2≤256*(m+1)*(S+1)*(K+1) at hd
  have hs := GeneralPaperScoreDPWork.scan_work
    (fun s => (GeneralPaperRayHighMinimum.candidate (GeneralPaperScoreDPWork.runWithWork S (fieldsRun matrix x w t).1).1 h s,12))
    (List.finRange (S+1)) 12 (fun _ _ => Nat.le_refl _)
  simp only [List.length_finRange] at hs
  have hA : 1≤(m+1)*(K+1) := Nat.mul_pos (by omega) (by omega)
  have hB := Nat.mul_le_mul_right (S+1) hA
  have hC : (m+1)*(K+1)≤(m+1)*(K+1)*(S+1) := by nlinarith only [Nat.zero_le ((m+1)*(K+1)*S)]
  change (fieldsRun matrix x w t).2+(GeneralPaperScoreDPWork.runWithWork S (fieldsRun matrix x w t).1).2+_+4*(S+1)+8≤_
  rw [fields_data]
  rw [fields_data] at hs
  nlinarith only [hf,hd,hs,hB,hC]

end Blotto.GeneralPaperRayQueryWork
