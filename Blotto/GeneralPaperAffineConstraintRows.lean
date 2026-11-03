import Blotto.GeneralPaperProxyRealResidualPaths

/-! The actual affine transfer constraints with zero anchors eliminated.
Box/adjacent-order constraints, retained original row budgets and every
tuple above the computed score threshold have integral sparse rows and
affine RHS constants/slopes. This finite index is an analysis polytope;
the runtime tests high tuples by the exact-score DP, not enumeration.
-/
namespace Blotto.GeneralPaperAffineConstraintRows
open RationalOrderCell
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Row (v : Type*) where
  terms : List (v × ℤ)
  constant : ℤ
  slope : ℤ

def Row.linear {v : Type*} (r : Row v) : LinearRow v := ⟨r.terms,0⟩

noncomputable def Row.coefficient {v : Type*} [DecidableEq v] (r : Row v) (j : v) : ℤ := coefficientTerms r.terms j

noncomputable def Row.bound {v : Type*} (r : Row v) (gamma : ℝ) : ℝ := (r.constant:ℝ)+gamma*(r.slope:ℝ)

noncomputable def Row.Holds {v : Type*} (r : Row v) (gamma : ℝ) (x : v → ℝ) : Prop :=
  r.linear.evaluate x≤r.bound gamma

abbrev HighTuple {m K : ℕ} (scores : Fin m → Fin K → ℕ) (threshold : ℕ) :=
  {labels : Fin m → Fin K // threshold<∑ j,scores j (labels j)}

abbrev Index (T m K : ℕ) (scores : Fin m → Fin K → ℕ) (threshold : ℕ) :=
  (Variable m K × Bool) ⊕ ((Fin m × Fin (K-1)) ⊕ (Fin T ⊕ HighTuple scores threshold))

def orderLeft {K : ℕ} (l : Fin (K-1)) : Fin (K+1) := ⟨l.val,by omega⟩
def orderRight {K : ℕ} (l : Fin (K-1)) : Fin (K+1) := ⟨l.val+1,by omega⟩

def constraints {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (threshold : ℕ) :
    Index T m K scores threshold → Row (Variable m K)
  | .inl (v,upper) => if upper then ⟨[(v,1)],1,0⟩ else ⟨[(v,-1)],0,0⟩
  | .inr (.inl (j,l)) => ⟨(rawRow (fun _ => 0) (.inl (j,orderLeft l,orderRight l))).terms,0,0⟩
  | .inr (.inr (.inl i)) => ⟨(rawRow (fun _ => 0) (.inr (labels i,0))).terms,1,0⟩
  | .inr (.inr (.inr l)) => ⟨(rawRow (fun _ => 0) (.inr (l.val,0))).neg.terms,0,-1⟩

noncomputable def Feasible {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (threshold : ℕ) (gamma : ℝ) (x : Variable m K → ℝ) : Prop :=
  ∀ i, (constraints labels scores threshold i).Holds gamma x

theorem variable_card (m K : ℕ) : Fintype.card (Variable m K)=m*(K-1) := by
  simp only [Variable,Fintype.card_prod,Fintype.card_fin]

theorem unit_terms {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (i : Index T m K scores h) : UnitTerms (constraints labels scores h i).linear := by
  rcases i with ⟨v,upper⟩|⟨j,l⟩|i|l
  · cases upper <;> intro term ht <;> simp only [constraints,Row.linear,Bool.false_eq_true,ite_false,ite_true,List.mem_singleton] at ht
    all_goals subst term; simp
  · exact rawRow_unitTerms (fun _ => 0) (.inl (j,orderLeft l,orderRight l))
  · exact rawRow_unitTerms (fun _ => 0) (.inr (labels i,0))
  · exact unitTerms_neg _ (rawRow_unitTerms (fun _ => 0) (.inr (l.val,0)))

theorem terms_length {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (i : Index T m K scores h) : (constraints labels scores h i).terms.length≤max m 2 := by
  rcases i with ⟨v,upper⟩|⟨j,l⟩|i|l
  · cases upper <;> simp only [constraints,Bool.false_eq_true,ite_false,ite_true,List.length_singleton] <;> omega
  · exact (rawRow_order_length (fun _ => 0) j (orderLeft l) (orderRight l)).trans (le_max_right _ _)
  · exact (rawRow_sum_length (fun _ => 0) (labels i) 0).trans (le_max_left _ _)
  · change (rawRow (fun _ => 0) (.inr (l.val,0))).neg.terms.length≤_
    simp only [LinearRow.neg,List.length_map]
    exact (rawRow_sum_length (fun _ => 0) l.val 0).trans (le_max_left _ _)

theorem coefficient_mass {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (i : Index T m K scores h) : (∑ j,((constraints labels scores h i).coefficient j).natAbs)≤max m 2 := by
  apply (coefficientTerms_mass (constraints labels scores h i).terms ?_).trans (terms_length labels scores h i)
  intro term ht
  rcases unit_terms labels scores h i term ht with he|he <;> simp [he]

theorem rhs_unit {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (i : Index T m K scores h) :
    (constraints labels scores h i).constant.natAbs≤1 ∧ (constraints labels scores h i).slope.natAbs≤1 := by
  rcases i with ⟨v,upper⟩|⟨j,l⟩|i|l
  · cases upper <;> norm_num [constraints]
  all_goals norm_num [constraints]

end Blotto.GeneralPaperAffineConstraintRows
