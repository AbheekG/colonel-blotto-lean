import Blotto.GeneralPaperBasisEntryBits

/-! Materialize the native next adjugate with bit-sensitive scalar entry
prices and explicit index/reference traffic at both matrix array levels.
Exact division remains a local premise, discharged by the valid cache join.
-/
namespace Blotto.GeneralPaperBasisUpdateBits
open GeneralPaperBasisStoredProducts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000

def rowRun {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j : Fin (n+1)) : Vector (n+1) × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (GeneralPaperBasisEntryBits.run primitive W D Dnext A au va j)

theorem row_data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) (j : Fin (n+1)) :
    (rowRun primitive W D Dnext A au va j).1=(GeneralPaperBasisStoredUpdate.rowRun D Dnext A au va j).1 := by
  simp only [rowRun,GeneralPaperBasisStoredUpdate.rowRun,PaperIndexedArrayConstruction.run_data,GeneralPaperBasisEntryBits.data]

theorem row_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H U V L : ℕ)
    (hW : 1≤W) (hN : binaryWordWidth (n+2)≤W) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k) (j : Fin (n+1)) :
    (rowRun primitive W D Dnext A au va j).2≤128*(n+2)*(W+primitive (1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L))) := by
  have hs := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => GeneralPaperBasisEntryBits.work primitive hMono W H U V L
    D Dnext A au va hD hNext hA hU hV hExact j k)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (GeneralPaperBasisEntryBits.run primitive W D Dnext A au va j)
  change (rowRun primitive W D Dnext A au va j).2≤_ at hh
  simp only [Nat.add_assoc,Nat.reduceAdd,Nat.mul_one] at hh
  have hO : 6*W+10*binaryWordWidth (n+2)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (n+2) hO
  nlinarith only [hs,hh,ho,Nat.zero_le (n*W),Nat.zero_le (n*primitive (1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L)))]

def run {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) : IntMatrix (n+1) × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W (rowRun primitive W D Dnext A au va)

theorem data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n) :
    (run primitive W D Dnext A au va).1=(GeneralPaperBasisStoredUpdate.matrixRun D Dnext A au va).1 := by
  simp only [run,GeneralPaperBasisStoredUpdate.matrixRun,PaperIndexedArrayConstruction.run_data,row_data]

theorem work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H U V L : ℕ)
    (hW : 1≤W) (hN : binaryWordWidth (n+2)≤W) (D Dnext : ℤ) (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k) :
    (run primitive W D Dnext A au va).2≤512*(n+2)^2*(W+primitive (1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L))) := by
  have hs := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) =>
    row_work primitive hMono W H U V L hW hN D Dnext A au va hD hNext hA hU hV hExact j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (rowRun primitive W D Dnext A au va)
  change (run primitive W D Dnext A au va).2≤_ at hh
  simp only [Nat.add_assoc,Nat.reduceAdd,Nat.mul_one] at hh
  have hO : 6*W+10*binaryWordWidth (n+2)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (n+2) hO
  nlinarith only [hs,hh,ho,Nat.zero_le (n*W),Nat.zero_le (n*primitive (1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L)))]

end Blotto.GeneralPaperBasisUpdateBits
