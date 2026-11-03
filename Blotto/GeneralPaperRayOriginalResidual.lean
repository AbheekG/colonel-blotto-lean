import Blotto.GeneralPaperRayHighSearch

/-! Evaluate the residual of any original affine transfer row at a fixed
budget. Its slope is exactly the original row applied to the direction;
high-tuple residuals agree with the fixed-predecessor tuple sums.
-/
namespace Blotto.GeneralPaperRayOriginalResidual
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 3500000

def evaluate {v : Type*} (r : Row v) (beta : ℚ) (x w : v → ℚ) : Affine :=
  let a := (GeneralPaperRaySparseEvaluation.evaluate r x w).1
  ⟨a.intercept-beta*(r.slope:ℚ),a.slope⟩

theorem value_data {v : Type*} (r : Row v) (beta : ℚ) (x w : v → ℚ) (t : ℚ) :
    (evaluate r beta x w).value t=(GeneralPaperRaySparseEvaluation.evaluate r x w).1.value t-beta*(r.slope:ℚ) := by
  dsimp only [evaluate,Affine.value]
  ring

theorem value_cast {v : Type*} (r : Row v) (beta : ℚ) (x w : v → ℚ) (t : ℚ) :
    ((evaluate r beta x w).value t:ℝ)=
      r.linear.evaluate (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))-r.bound (beta:ℝ) := by
  rw [value_data,Rat.cast_sub,Rat.cast_mul,Rat.cast_intCast,GeneralPaperRaySparseEvaluation.residual_on_ray]
  unfold Row.bound
  ring

theorem slope_cast {v : Type*} (r : Row v) (beta : ℚ) (x w : v → ℚ) :
    ((evaluate r beta x w).slope:ℝ)=r.linear.evaluate (fun j => (w j:ℝ)) := by
  change (((GeneralPaperRaySparseEvaluation.evaluate r x w).1.slope:ℚ):ℝ)=_
  rw [(GeneralPaperRaySparseEvaluation.evaluate_data r x w).2]
  exact GeneralPaperRaySparseEvaluation.linear_cast r.terms w

theorem static_eq {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (beta : ℚ) (x w : Variable m K → ℚ)
    (i : GeneralPaperStaticRayRows.StaticIndex T m K) :
    evaluate (GeneralPaperStaticRayRows.row labels i) beta x w=(GeneralPaperStaticRayScan.evaluate labels x w i).1 := by
  simp only [evaluate,GeneralPaperStaticRaySound.row_slope_zero,Int.cast_zero,mul_zero,sub_zero,GeneralPaperStaticRayScan.evaluate]

theorem high_value {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (l : HighTuple scores h) (beta : ℚ) (x w : Variable m K → ℚ) (t : ℚ) :
    (evaluate (constraints labels scores h (.inr (.inr (.inr l)))) beta x w).value t=
      (GeneralPaperRayTupleResidual.residual x w beta l.val).value t := by
  have hLeft := value_cast (constraints labels scores h (.inr (.inr (.inr l)))) beta x w t
  have hRow : (constraints labels scores h (.inr (.inr (.inr l)))).linear.evaluate
      (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))= -tupleSum (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ)) l.val := by
    change (rawRow (fun _ => 0) (.inr (l.val,0))).neg.evaluate _=_
    rw [LinearRow.evaluate_neg,GeneralPaperAffineConstraintSemantics.tuple_evaluate]
  rw [hRow] at hLeft
  simp only [Row.bound,constraints,Int.cast_zero,Int.cast_neg,Int.cast_one,mul_neg_one,zero_add] at hLeft
  have hRight : ((GeneralPaperRayTupleResidual.residual x w beta l.val).value t:ℝ)=
      (beta:ℝ)-tupleSum (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ)) l.val := by
    rw [GeneralPaperRayTupleResidual.residual_value,Rat.cast_sub,GeneralPaperRayAnchorCosts.tuple_cast]
  have hh : ((evaluate (constraints labels scores h (.inr (.inr (.inr l)))) beta x w).value t:ℝ)=
      ((GeneralPaperRayTupleResidual.residual x w beta l.val).value t:ℝ) := by
    calc
      _ = -tupleSum (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ)) l.val- -(beta:ℝ) := hLeft
      _ = _ := by rw [hRight]; ring
  exact_mod_cast hh

end Blotto.GeneralPaperRayOriginalResidual
