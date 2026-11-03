import Blotto.GeneralPaperAffineConstraintRows

/-! One affine RHS column increases the actual constraint row mass to
at most m+1. Bounds are case-specific: an order row has no affine RHS,
while a tuple row has at most m nonzero terms. No factorial loss is used.
-/
namespace Blotto.GeneralPaperAffineConstraintMass
open RationalOrderCell GeneralPaperAffineConstraintRows
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

def rhs {v : Type*} (r : Row v) (useSlope : Bool) : ℤ := if useSlope then r.slope else r.constant

theorem augmented_terms {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (i : Index T m K scores h) (useSlope : Bool) :
    (constraints labels scores h i).terms.length+(rhs (constraints labels scores h i) useSlope).natAbs≤m+1 := by
  rcases i with ⟨v,upper⟩|⟨j,l⟩|i|l
  · cases upper <;> cases useSlope
    all_goals norm_num [constraints,rhs]
    all_goals omega
  · have hl := rawRow_order_length (fun _ => 0) j (orderLeft l) (orderRight l)
    cases useSlope <;> simpa only [constraints,rhs,Bool.false_eq_true,ite_true,ite_false,Int.natAbs_zero,Nat.add_zero] using hl.trans (by omega : 2≤m+1)
  · have hl := rawRow_sum_length (fun _ => 0) (labels i) 0
    cases useSlope <;> simp only [constraints,rhs,Bool.false_eq_true,ite_true,ite_false,Int.natAbs_zero,Int.natAbs_one,Nat.add_zero] <;> omega
  · have hl := rawRow_sum_length (fun _ => 0) l.val 0
    cases useSlope <;> simp only [constraints,rhs,Bool.false_eq_true,LinearRow.neg,List.length_map,ite_true,ite_false,Int.natAbs_zero,Int.natAbs_neg,Int.natAbs_one,Nat.add_zero] <;> omega

theorem augmented_mass {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (i : Index T m K scores h) (useSlope : Bool) :
    (∑ j,((constraints labels scores h i).coefficient j).natAbs)+
      (rhs (constraints labels scores h i) useSlope).natAbs≤m+1 := by
  have hc : (∑ j,((constraints labels scores h i).coefficient j).natAbs)≤(constraints labels scores h i).terms.length := by
    apply coefficientTerms_mass
    intro term ht
    rcases unit_terms labels scores h i term ht with he|he <;> simp [he]
  exact (Nat.add_le_add_right hc _).trans (augmented_terms hm labels scores h i useSlope)

end Blotto.GeneralPaperAffineConstraintMass
