import Blotto.GeneralPaperBasisPositiveUpdate

/-! Source arithmetic and retained-matrix entry counts for the actual
integer update. This is the adjugate-update component, not yet the full
basis controller, fresh solve, bit or simultaneous-space ledger.
-/
namespace Blotto.GeneralPaperBasisUpdateLedger
open GeneralPaperBasisStoredProducts GeneralPaperBasisStoredStep
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem updates_work (d : ℕ) (D : Fin d → ℤ) (A : ∀ j : Fin d,IntMatrix j.val)
    (u v : ∀ j : Fin d,Vector j.val) (a : Fin d → ℤ) :
    (∑ j : Fin d,(run (D j) (A j) (u j) (v j) (a j)).work)≤1024*d*(d+1)^2 := by
  have hEach (j : Fin d) : (run (D j) (A j) (u j) (v j) (a j)).work≤1024*(d+1)^2 := by
    have hj : j.val+2≤d+1 := by have hh := j.isLt; omega
    have hp : (j.val+2)^2≤(d+1)^2 := by simpa only [pow_two] using Nat.mul_le_mul hj hj
    exact (run_work (D j) (A j) (u j) (v j) (a j)).trans (Nat.mul_le_mul_left 1024 hp)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hEach j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  have he : d*(1024*(d+1)^2)=1024*d*(d+1)^2 := by ring
  rwa [he] at hs

def entries {n : ℕ} (A : IntMatrix n) : ℕ := ∑ j : Fin n,(A.read j).data.size

theorem entries_exact {n : ℕ} (A : IntMatrix n) : entries A=n^2 := by
  have hSize (j : Fin n) : (A.read j).data.size=n := (A.read j).size
  simp only [entries,hSize,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,pow_two]

theorem output_entries {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) :
    entries (run D A u v a).adjugate=(n+1)^2 := entries_exact _

end Blotto.GeneralPaperBasisUpdateLedger
