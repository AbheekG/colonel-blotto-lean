import Blotto.GeneralPaperTransferPolytopePoint

/-! Cofactors of every actual defining matrix satisfy the same uniform
root envelope. Replacing one row by a unit row computes the adjugate entry;
the original per-row mass bound is preserved, including singular systems.
-/
namespace Blotto.GeneralPaperTransferCofactorBounds
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperTransferMatrices
open GeneralPaperTransferDeterminantBounds
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem row_mass {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h) (i : Variable m K) :
    (∑ j,((matrix labels scores h selected) i j).natAbs)≤m+1 := by
  have ha := GeneralPaperAffineConstraintMass.augmented_mass hm labels scores h (selected i) false
  change (∑ j,((constraints labels scores h (selected i)).coefficient j).natAbs)≤_
  omega

theorem cofactor_bound {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h) (i j : Variable m K) :
    ((matrix labels scores h selected).adjugate i j).natAbs≤(m+1)^(m*(K-1)) := by
  rw [Matrix.adjugate_apply]
  apply (FinitePolytopeRationalWitness.det_natAbs_le_rowMass _).trans
  have hr (r : Variable m K) :
      (∑ c,(((matrix labels scores h selected).updateRow j (Pi.single i 1)) r c).natAbs)≤m+1 := by
    by_cases he : r=j
    · subst r
      simp only [Matrix.updateRow_self]
      simp only [Pi.single_apply,apply_ite Int.natAbs,Int.natAbs_one,Int.natAbs_zero]
      simp
    · rw [Matrix.updateRow_ne he]
      exact row_mass hm labels scores h selected r
  have hp := Finset.prod_le_prod (s:=Finset.univ) (fun r _ => hr r)
  simpa only [Finset.prod_const,Finset.card_univ,variable_card] using hp

end Blotto.GeneralPaperTransferCofactorBounds
