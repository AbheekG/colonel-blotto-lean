import Blotto.GeneralPaperStaticRayScan

/-! The actual sparse static scan gives the maximal forward static-feasible
interval and an original tight positive-derivative blocker. A coordinate
velocity of one derives finiteness and the upper bound one; no endpoint or
strict-interiority oracle is supplied. High-tuple tests remain a separate
endpoint-search join.
-/
namespace Blotto.GeneralPaperStaticRaySound
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStaticRayRows GeneralPaperStaticRayScan
open GeneralPaperRayAffine GeneralPaperRayMinimumSound
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem row_slope_zero {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (i : StaticIndex T m K) :
    (row labels i).slope=0 := by
  rcases i with ⟨v,b⟩|v|i
  · cases b <;> rfl
  all_goals rfl

noncomputable def StaticFeasible {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (gamma : ℝ)
    (x w : Variable m K → ℚ) (t : ℚ) : Prop :=
  ∀ i : StaticIndex T m K, (row labels i).Holds gamma (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))

theorem residual_cast {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (gamma : ℝ)
    (x w : Variable m K → ℚ) (t : ℚ) (i : StaticIndex T m K) :
    (((evaluate labels x w i).1.value t:ℚ):ℝ)=
      (row labels i).linear.evaluate (fun j => (x j:ℝ)+(t:ℝ)*(w j:ℝ))-(row labels i).bound gamma := by
  have he := GeneralPaperRaySparseEvaluation.residual_on_ray (row labels i) x w t
  simpa only [evaluate,Row.bound,row_slope_zero,Int.cast_zero,mul_zero,add_zero] using he

theorem initial_residual {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (gamma : ℝ) (x w : Variable m K → ℚ)
    (hStart : GeneralPaperAffineConstraintRows.Feasible labels scores h gamma (fun j => (x j:ℝ)))
    (i : StaticIndex T m K) : (evaluate labels x w i).1.intercept≤0 := by
  have he := residual_cast labels gamma x w 0 i
  simp only [Affine.value,mul_zero,add_zero,Rat.cast_zero,zero_mul] at he
  have hh := hStart (embed i)
  rw [←row_eq labels scores h i] at hh
  have hr : (((evaluate labels x w i).1.intercept:ℚ):ℝ)≤0 := by
    rw [he]
    exact sub_nonpos.mpr hh
  exact_mod_cast hr

theorem forward_static {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (gamma : ℝ) (x w : Variable m K → ℚ)
    (hStart : GeneralPaperAffineConstraintRows.Feasible labels scores h gamma (fun j => (x j:ℝ)))
    (c : GeneralPaperRayMinimum.Choice (StaticIndex T m K)) (hc : (scan labels x w).choice=some c)
    (t : ℚ) (ht : 0≤t ∧ t≤c.time) : StaticFeasible labels gamma x w t := by
  intro i
  have hh := forward_feasible (evaluate labels x w) (enumerate T m K)
    (fun j _ => initial_residual labels scores h gamma x w hStart j) c hc t ht i (enumerate_mem i)
  have hr : (((evaluate labels x w i).1.value t:ℚ):ℝ)≤0 := by exact_mod_cast hh
  rw [residual_cast] at hr
  exact sub_nonpos.mp hr

theorem beyond_static {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (gamma : ℝ)
    (x w : Variable m K → ℚ) (c : GeneralPaperRayMinimum.Choice (StaticIndex T m K))
    (hc : (scan labels x w).choice=some c) (t : ℚ) (ht : c.time<t) : ¬StaticFeasible labels gamma x w t := by
  intro hf
  have hp := beyond_infeasible (evaluate labels x w) (enumerate T m K) c hc t ht
  have hr : (0:ℝ)<(evaluate labels x w c.blocker).1.value t := by exact_mod_cast hp
  rw [residual_cast] at hr
  have hh := hf c.blocker
  change _≤_ at hh
  linarith only [hr,hh]

theorem upper_affine {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x w : Variable m K → ℚ) (v : Variable m K) :
    (evaluate labels x w (.inl (v,true))).1.intercept=x v-1 ∧
      (evaluate labels x w (.inl (v,true))).1.slope=w v := by
  simp only [evaluate,row,constraints,embed,ite_true,GeneralPaperRaySparseEvaluation.evaluate,
    GeneralPaperRaySparseEvaluation.loop,zero_add,Int.cast_one,one_mul,and_self]

theorem finite_endpoint {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (gamma : ℝ) (x w : Variable m K → ℚ)
    (hStart : GeneralPaperAffineConstraintRows.Feasible labels scores h gamma (fun j => (x j:ℝ)))
    (v : Variable m K) (hVelocity : w v=1) :
    ∃ c : GeneralPaperRayMinimum.Choice (StaticIndex T m K), (scan labels x w).choice=some c ∧
      0≤c.time ∧ c.time≤1 ∧ 0<(evaluate labels x w c.blocker).1.slope ∧
      (evaluate labels x w c.blocker).1.value c.time=0 := by
  have hu := upper_affine labels x w v
  have hp : 0<(evaluate labels x w (.inl (v,true))).1.slope := by rw [hu.2,hVelocity]; norm_num
  obtain ⟨c,hc⟩ := exists_selected (evaluate labels x w) (enumerate T m K) (.inl (v,true)) (enumerate_mem _) hp
  have hs := selected (evaluate labels x w) (enumerate T m K) c hc
  have hCap := hs.2.2.2 (.inl (v,true)) (enumerate_mem _) hp
  have hx : 0≤x v := by
    have hb := hStart (.inl (v,false))
    have hh := (GeneralPaperAffineConstraintSemantics.box_holds labels scores h v false gamma (fun j => (x j:ℝ))).mp hb
    exact_mod_cast hh
  have hCross : (evaluate labels x w (.inl (v,true))).1.crossing=1-x v := by
    rw [Affine.crossing,hu.1,hu.2,hVelocity,div_one]
    ring
  rw [hCross] at hCap
  refine ⟨c,hc,endpoint_nonnegative _ _ (fun j _ => initial_residual labels scores h gamma x w hStart j) c hc,
    by linarith only [hCap,hx],hs.2.2.1,endpoint_tight _ _ c hc⟩

end Blotto.GeneralPaperStaticRaySound
