import Blotto.GeneralPaperTransferMatrices

/-! The constructed integral affine rows express exactly the paper's
four constraint families. Zero labels are fixed, adjacent labels impose
their actual order, and the original whole-row label table is retained.
-/
namespace Blotto.GeneralPaperAffineConstraintSemantics
open RationalOrderCell GeneralPaperAffineConstraintRows
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem box_holds {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (v : Variable m K) (upper : Bool) (gamma : ℝ) (x : Variable m K → ℝ) :
    (constraints labels scores h (.inl (v,upper))).Holds gamma x ↔ if upper then x v≤1 else 0≤x v := by
  cases upper <;> simp only [constraints,Row.Holds,Row.linear,LinearRow.evaluate,Row.bound,
    Bool.false_eq_true,ite_false,ite_true,List.map_singleton,List.sum_singleton,Int.cast_one,Int.cast_neg,Int.cast_zero,
    one_mul,neg_mul,mul_zero,add_zero,neg_nonpos]

theorem order_bound_zero {m K : ℕ} (j : Fin m) (l : Fin (K-1)) :
    (rawRow (fun _ => 0) (.inl (j,orderLeft l,orderRight l))).bound=0 := by
  have hl : refBound (reference j (orderLeft l))=0 := tupleReference_bound j (⟨l.val,by omega⟩:Fin K)
  have hr : refBound (reference j (orderRight l))=0 := tupleReference_bound j (⟨l.val+1,by omega⟩:Fin K)
  change refBound (reference j (orderRight l))-refBound (reference j (orderLeft l))=0
  rw [hr,hl,sub_self]

theorem order_holds {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (j : Fin m) (l : Fin (K-1)) (gamma : ℝ) (x : Variable m K → ℝ) :
    (constraints labels scores h (.inr (.inl (j,l)))).Holds gamma x ↔
      anchor x j (orderLeft l)≤anchor x j (orderRight l) := by
  have he := rawRow_order (fun _ => 0) x j (orderLeft l) (orderRight l)
  rw [LinearRow.residual,order_bound_zero,Rat.cast_zero,sub_zero] at he
  simp only [Row.Holds,Row.bound,constraints,Int.cast_zero,mul_zero,add_zero]
  change (rawRow (fun _ => 0) (.inl (j,orderLeft l,orderRight l))).evaluate x≤0 ↔ _
  rw [he]
  exact sub_nonpos

theorem tuple_evaluate {m K : ℕ} (x : Variable m K → ℝ) (l : Fin m → Fin K) :
    (rawRow (fun _ => 0) (.inr (l,0))).evaluate x=tupleSum x l := by
  have he := rawRow_sum (fun _ => 0) x l 0
  simpa only [LinearRow.residual,rawRow,Rat.cast_zero,sub_zero] using he

theorem retained_row_holds {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (i : Fin T) (gamma : ℝ) (x : Variable m K → ℝ) :
    (constraints labels scores h (.inr (.inr (.inl i)))).Holds gamma x ↔ tupleSum x (labels i)≤1 := by
  simp only [Row.Holds,Row.bound,constraints,Int.cast_zero,Int.cast_one,mul_zero,add_zero]
  change (rawRow (fun _ => 0) (.inr (labels i,0))).evaluate x≤1 ↔ _
  rw [tuple_evaluate]

theorem high_tuple_holds {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (l : HighTuple scores h) (gamma : ℝ) (x : Variable m K → ℝ) :
    (constraints labels scores h (.inr (.inr (.inr l)))).Holds gamma x ↔ gamma≤tupleSum x l.val := by
  simp only [Row.Holds,Row.bound,constraints,Int.cast_zero,Int.cast_one,Int.cast_neg,mul_neg_one,zero_add]
  change (rawRow (fun _ => 0) (.inr (l.val,0))).neg.evaluate x≤-gamma ↔ _
  rw [LinearRow.evaluate_neg,tuple_evaluate]
  exact neg_le_neg_iff

theorem feasible_iff {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (gamma : ℝ) (x : Variable m K → ℝ) : GeneralPaperAffineConstraintRows.Feasible labels scores h gamma x ↔
    (∀ v,0≤x v ∧ x v≤1) ∧
    (∀ j l,anchor x j (orderLeft l)≤anchor x j (orderRight l)) ∧
    (∀ i,tupleSum x (labels i)≤1) ∧
    (∀ l : HighTuple scores h,gamma≤tupleSum x l.val) := by
  constructor
  · intro hx
    refine ⟨?_,?_,?_,?_⟩
    · intro v
      exact ⟨(box_holds labels scores h v false gamma x).mp (hx (.inl (v,false))),
        (box_holds labels scores h v true gamma x).mp (hx (.inl (v,true)))⟩
    · intro j l
      exact (order_holds labels scores h j l gamma x).mp (hx (.inr (.inl (j,l))))
    · intro i
      exact (retained_row_holds labels scores h i gamma x).mp (hx (.inr (.inr (.inl i))))
    · intro l
      exact (high_tuple_holds labels scores h l gamma x).mp (hx (.inr (.inr (.inr l))))
  · rintro ⟨hb,ho,hr,hh⟩ i
    rcases i with ⟨v,upper⟩|⟨j,l⟩|i|l
    · apply (box_holds labels scores h v upper gamma x).mpr
      cases upper
      · exact (hb v).1
      · exact (hb v).2
    · exact (order_holds labels scores h j l gamma x).mpr (ho j l)
    · exact (retained_row_holds labels scores h i gamma x).mpr (hr i)
    · exact (high_tuple_holds labels scores h l gamma x).mpr (hh l)

end Blotto.GeneralPaperAffineConstraintSemantics
