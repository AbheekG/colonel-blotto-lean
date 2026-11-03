import Blotto.GeneralPaperStaticRayRows

/-! One sparse pass evaluates both the starting residual and velocity.
The executable loop uses the literal original terms, not a dense matrix or
an externally supplied residual. Coefficient aggregation is proof-only.
-/
namespace Blotto.GeneralPaperRaySparseEvaluation
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Sums where
  point : ℚ
  velocity : ℚ
  work : ℕ

def loop {v : Type*} (x w : v → ℚ) : List (v × ℤ) → ℚ → ℚ → ℕ → Sums
  | [],a,b,spent => ⟨a,b,spent+2⟩
  | term::rest,a,b,spent =>
      loop x w rest (a+(term.2:ℚ)*x term.1) (b+(term.2:ℚ)*w term.1) (spent+12)

def evaluate {v : Type*} (r : Row v) (x w : v → ℚ) : Affine × ℕ :=
  let sums := loop x w r.terms 0 0 0
  (⟨sums.point-(r.constant:ℚ),sums.velocity⟩,sums.work+8)

theorem loop_data {v : Type*} (x w : v → ℚ) (terms : List (v × ℤ)) (a b : ℚ) (spent : ℕ) :
    (loop x w terms a b spent).point=a+(terms.map (fun term => (term.2:ℚ)*x term.1)).sum ∧
    (loop x w terms a b spent).velocity=b+(terms.map (fun term => (term.2:ℚ)*w term.1)).sum ∧
    (loop x w terms a b spent).work=spent+12*terms.length+2 := by
  induction terms generalizing a b spent with
  | nil => exact ⟨by simp [loop],by simp [loop],rfl⟩
  | cons term rest ih =>
    have hh := ih (a+(term.2:ℚ)*x term.1) (b+(term.2:ℚ)*w term.1) (spent+12)
    change _ ∧ _ ∧ _
    simp only [loop,List.map_cons,List.sum_cons,List.length_cons]
    exact ⟨by rw [hh.1]; ring,by rw [hh.2.1]; ring,by rw [hh.2.2]; omega⟩

theorem evaluate_data {v : Type*} (r : Row v) (x w : v → ℚ) :
    (evaluate r x w).1.intercept=(r.terms.map (fun term => (term.2:ℚ)*x term.1)).sum-(r.constant:ℚ) ∧
    (evaluate r x w).1.slope=(r.terms.map (fun term => (term.2:ℚ)*w term.1)).sum := by
  have hh := loop_data x w r.terms 0 0 0
  exact ⟨by simpa only [evaluate,zero_add] using congrArg (fun a : ℚ => a-(r.constant:ℚ)) hh.1,
    by simpa only [evaluate,zero_add] using hh.2.1⟩

theorem evaluate_work {v : Type*} (r : Row v) (x w : v → ℚ) : (evaluate r x w).2=12*r.terms.length+10 := by
  have hh := (loop_data x w r.terms 0 0 0).2.2
  change (loop x w r.terms 0 0 0).work+8=_
  omega

theorem linear_cast {v : Type*} (terms : List (v × ℤ)) (x : v → ℚ) :
    (((terms.map (fun term => (term.2:ℚ)*x term.1)).sum:ℚ):ℝ)=
      (LinearRow.mk terms 0).evaluate (fun j => (x j:ℝ)) := by
  induction terms with
  | nil => simp only [List.map_nil,List.sum_nil,Rat.cast_zero,LinearRow.evaluate]
  | cons term rest ih =>
    simp only [List.map_cons,List.sum_cons,Rat.cast_add,Rat.cast_mul,Rat.cast_intCast,LinearRow.evaluate]
    rw [ih]
    rfl

theorem residual_on_ray {v : Type*} (r : Row v) (x w : v → ℚ) (t : ℚ) :
    (((evaluate r x w).1.value t:ℚ):ℝ)=
      r.linear.evaluate (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))-(r.constant:ℝ) := by
  rw [Affine.value,(evaluate_data r x w).1,(evaluate_data r x w).2]
  simp only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_intCast,linear_cast]
  have he : r.linear.evaluate (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))=
      r.linear.evaluate (fun j => (x j:ℝ))+(t:ℝ)*r.linear.evaluate (fun j => (w j:ℝ)) := by
    suffices hTerms : ∀ terms : List (v × ℤ),
        (LinearRow.mk terms 0).evaluate (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))=
          (LinearRow.mk terms 0).evaluate (fun j => (x j:ℝ))+(t:ℝ)*(LinearRow.mk terms 0).evaluate (fun j => (w j:ℝ)) from
      hTerms r.terms
    intro terms
    induction terms with
    | nil => simp only [LinearRow.evaluate,List.map_nil,List.sum_nil,mul_zero,add_zero]
    | cons term rest ih =>
      change (term.2:ℝ)*((x term.1:ℝ)+(t:ℝ)*(w term.1:ℝ))+
        (LinearRow.mk rest 0).evaluate (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))=_
      rw [ih]
      simp only [LinearRow.evaluate,List.map_cons,List.sum_cons]
      ring
  rw [he]
  dsimp only [Row.linear]
  ring

end Blotto.GeneralPaperRaySparseEvaluation
