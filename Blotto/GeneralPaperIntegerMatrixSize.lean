import Blotto.GeneralPaperEndpointDictionaryBits

/-! Row-mass determinant, adjugate and Cramer bounds. These are proof-only
observers: the executed compiler retains its exact integer cache and never
computes a determinant/adjugate from scratch to establish a size bound.
-/
namespace Blotto.GeneralPaperIntegerMatrixSize
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem determinant {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ) (B : ℕ)
    (hRows : ∀ r,(∑ c,(M r c).natAbs)≤B) : M.det.natAbs≤B^(Fintype.card i) := by
  apply (FinitePolytopeRationalWitness.det_natAbs_le_rowMass M).trans
  have hh := Finset.prod_le_prod (s:=Finset.univ) (fun r _ => hRows r)
  simpa only [Finset.prod_const,Finset.card_univ] using hh

theorem adjugate {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ) (B : ℕ) (hB : 1≤B)
    (hRows : ∀ r,(∑ c,(M r c).natAbs)≤B) (a b : i) : (M.adjugate a b).natAbs≤B^(Fintype.card i) := by
  rw [Matrix.adjugate_apply]
  apply determinant
  intro r
  by_cases hr : r=b
  · subst r
    simpa only [Matrix.updateRow_self,Pi.single_apply,apply_ite Int.natAbs,Int.natAbs_one,Int.natAbs_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hB
  · simpa only [Matrix.updateRow_ne hr] using hRows r

theorem replaced_column_mass {i : Type*} [Fintype i] [DecidableEq i]
    (M : Matrix i i ℤ) (b : i → ℤ) (j r : i) :
    (∑ c,((M.updateCol j b) r c).natAbs)≤(∑ c,(M r c).natAbs)+(b r).natAbs := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => show
      ((M.updateCol j b) r c).natAbs≤(M r c).natAbs+(if c=j then (b r).natAbs else 0) from by
    by_cases hc : c=j
    · simp only [Matrix.updateCol_apply,hc,ite_true]
      omega
    · simp only [Matrix.updateCol_apply,hc,ite_false,Nat.add_zero,le_refl])
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh

theorem cramer {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ) (b : i → ℤ) (B : ℕ)
    (hRows : ∀ r,(∑ c,(M r c).natAbs)+(b r).natAbs≤B) (j : i) :
    (M.adjugate.mulVec b j).natAbs≤B^(Fintype.card i) := by
  rw [←Matrix.cramer_eq_adjugate_mulVec,Matrix.cramer_apply]
  exact determinant _ B (fun r => (replaced_column_mass M b j r).trans (hRows r))

end Blotto.GeneralPaperIntegerMatrixSize
