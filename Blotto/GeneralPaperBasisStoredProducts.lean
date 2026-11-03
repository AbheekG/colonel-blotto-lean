import Blotto.GeneralPaperBasisIntegerDot

/-! Actual stored integer matrix-vector and row-matrix products. Each
entry executes one tail dot product and the indexed constructor stores
the result once. Prices are paper arithmetic/indexed-source operations.
-/
namespace Blotto.GeneralPaperBasisStoredProducts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev Vector (n : ℕ) := FixedArrayTable n ℤ
abbrev IntMatrix (n : ℕ) := FixedArrayTable n (Vector n)

def observe {n : ℕ} (A : IntMatrix n) : Matrix (Fin n) (Fin n) ℤ := fun j k => (A.read j).read k

def mulVecRun {n : ℕ} (A : IntMatrix n) (u : Vector n) : Vector n × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun j =>
    let result := GeneralPaperBasisIntegerDot.run (fun k => (A.read j).read k) u.read
    (result.value,result.work+4))

def rowRun {n : ℕ} (v : Vector n) (A : IntMatrix n) : Vector n × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun k =>
    let result := GeneralPaperBasisIntegerDot.run v.read (fun j => (A.read j).read k)
    (result.value,result.work+4))

theorem mulVec_data {n : ℕ} (A : IntMatrix n) (u : Vector n) : (mulVecRun A u).1.read=(observe A).mulVec u.read := by
  funext j
  simp only [mulVecRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,GeneralPaperBasisIntegerDot.run_value]
  rfl

theorem row_data {n : ℕ} (v : Vector n) (A : IntMatrix n) :
    (rowRun v A).1.read=GeneralPaperBasisAdjugateBlock.rowProduct v.read (observe A) := by
  funext j
  simp only [rowRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,GeneralPaperBasisIntegerDot.run_value]
  rfl

theorem mulVec_work {n : ℕ} (A : IntMatrix n) (u : Vector n) : (mulVecRun A u).2≤128*(n+1)^2 := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun j => ((GeneralPaperBasisIntegerDot.run (fun k => (A.read j).read k) u.read).value,
      (GeneralPaperBasisIntegerDot.run (fun k => (A.read j).read k) u.read).work+4))
  change (mulVecRun A u).2≤(∑ j : Fin n,((GeneralPaperBasisIntegerDot.run (fun k => (A.read j).read k) u.read).work+4))+
    (n+1)*(6+10*0*binaryWordWidth (n+1)+28) at hh
  have hs : (∑ j : Fin n,((GeneralPaperBasisIntegerDot.run (fun k => (A.read j).read k) u.read).work+4))=n*(16*n+6+4) := by
    simp only [GeneralPaperBasisIntegerDot.run_work,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]
  rw [hs] at hh
  norm_num only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.reduceAdd] at hh
  nlinarith only [hh]

theorem row_work {n : ℕ} (v : Vector n) (A : IntMatrix n) : (rowRun v A).2≤128*(n+1)^2 := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun k => ((GeneralPaperBasisIntegerDot.run v.read (fun j => (A.read j).read k)).value,
      (GeneralPaperBasisIntegerDot.run v.read (fun j => (A.read j).read k)).work+4))
  change (rowRun v A).2≤(∑ k : Fin n,((GeneralPaperBasisIntegerDot.run v.read (fun j => (A.read j).read k)).work+4))+
    (n+1)*(6+10*0*binaryWordWidth (n+1)+28) at hh
  have hs : (∑ k : Fin n,((GeneralPaperBasisIntegerDot.run v.read (fun j => (A.read j).read k)).work+4))=n*(16*n+6+4) := by
    simp only [GeneralPaperBasisIntegerDot.run_work,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]
  rw [hs] at hh
  norm_num only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.reduceAdd] at hh
  nlinarith only [hh]

end Blotto.GeneralPaperBasisStoredProducts
