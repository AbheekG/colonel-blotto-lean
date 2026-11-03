import Blotto.Model

/-! Exact pure-allocation arithmetic for the two-battlefield security
counterexample in the general appendix. The mixed weak-topology and
literature-hypothesis claims require separate treatment. -/
namespace Blotto.GeneralPaperSecurityCounterexample
set_option autoImplicit false

noncomputable def values : Values 2 where
  weight := ![(1/2:ℝ),1/2]
  positive := by intro j; fin_cases j <;> norm_num
  normalized := by norm_num [Fin.sum_univ_two]

noncomputable def xStar : Allocation 2 := ![(1/3:ℝ),2/3]
noncomputable def yStar : Allocation 2 := ![(1/3:ℝ),0]
noncomputable def xMove (t : ℝ) : Allocation 2 := ![(1/3:ℝ)+t,2/3-t]
noncomputable def xDominant : Allocation 2 := ![(1/2:ℝ),1/2]

theorem feasible_xStar : Feasible 1 xStar := by
  constructor
  · intro j; fin_cases j <;> norm_num [xStar]
  · norm_num [xStar,Fin.sum_univ_two]

theorem feasible_yStar : Feasible (1/3:ℝ) yStar := by
  constructor
  · intro j; fin_cases j <;> norm_num [yStar]
  · norm_num [yStar,Fin.sum_univ_two]

theorem feasible_xMove (t : ℝ) (ht : 0<t ∧ t<1/3) :
    Feasible 1 (xMove t) := by
  constructor
  · intro j; fin_cases j <;> simp [xMove] <;> linarith
  · norm_num [xMove,Fin.sum_univ_two]

theorem at_star : payoff values xStar yStar=3/4 ∧
    payoff values yStar xStar=1/4 := by
  constructor
  · norm_num [payoff,values,xStar,yStar,share,Fin.sum_univ_two]
  · norm_num [payoff,values,xStar,yStar,share,Fin.sum_univ_two]

theorem moved_dominates (t : ℝ) (ht : 0<t ∧ t<1/3)
    (y : Allocation 2) (hy : Feasible (1/3:ℝ) y) :
    payoff values (xMove t) y=1 ∧ payoff values y (xMove t)=0 := by
  have h0 : y 0≤1/3 := by
    have hs:=hy.2
    simp only [Fin.sum_univ_two] at hs
    linarith [hy.1 1]
  have h1 : y 1≤1/3 := by
    have hs:=hy.2
    simp only [Fin.sum_univ_two] at hs
    linarith [hy.1 0]
  have hw : payoff values (xMove t) y=1 := by
    have hleft : y 0<1/3+t := by linarith
    have hright : y 1<2/3-t := by linarith
    have hshare0 : share ((xMove t) 0) (y 0)=1 := by
      change y 0<(xMove t) 0 at hleft
      simp only [share,hleft,ite_true]
    have hshare1 : share ((xMove t) 1) (y 1)=1 := by
      change y 1<(xMove t) 1 at hright
      simp only [share,hright,ite_true]
    norm_num [payoff,Fin.sum_univ_two,values,hshare0,hshare1]
  exact ⟨hw,by linarith [payoff_constant_sum values (xMove t) y]⟩

theorem moved_at_star (t : ℝ) (ht : 0<t ∧ t<1/3) :
    payoff values (xMove t) yStar=1 ∧
    payoff values yStar (xMove t)=0 :=
  moved_dominates t ht yStar feasible_yStar

theorem star_has_profitable_deviation :
    ∃ z : Allocation 2,Feasible 1 z ∧
      payoff values xStar yStar < payoff values z yStar := by
  refine ⟨xMove (1/6),feasible_xMove (1/6) (by norm_num),?_⟩
  rw [(at_star).1,(moved_at_star (1/6) (by norm_num)).1]
  norm_num

theorem moved_profiles_arbitrarily_close (delta : ℝ) (hd : 0<delta) :
    ∃ t : ℝ,0<t ∧ t<1/3 ∧
      ∀ j : Fin 2,|xMove t j-xStar j|<delta := by
  let t:=min (delta/2) (1/6)
  have ht : 0<t ∧ t<1/3 := by
    dsimp only [t]
    constructor
    · exact lt_min (by linarith) (by norm_num)
    · have h:=min_le_right (delta/2) (1/6:ℝ)
      linarith
  have htd : t<delta := by
    have h:=min_le_left (delta/2) (1/6:ℝ)
    dsimp only [t]
    linarith
  refine ⟨t,ht.1,ht.2,?_⟩
  intro j
  fin_cases j
  · simpa [xMove,xStar,abs_of_pos ht.1] using htd
  · simpa [xMove,xStar,abs_neg,abs_of_pos ht.1] using htd

theorem dominant_feasible : Feasible 1 xDominant := by
  constructor
  · intro j; fin_cases j <;> norm_num [xDominant]
  · norm_num [xDominant,Fin.sum_univ_two]

theorem dominant_wins (y : Allocation 2) (hy : Feasible (1/3:ℝ) y) :
    payoff values xDominant y=1 ∧ payoff values y xDominant=0 := by
  have h0 : y 0≤1/3 := by
    have hs:=hy.2
    simp only [Fin.sum_univ_two] at hs
    linarith [hy.1 1]
  have h1 : y 1≤1/3 := by
    have hs:=hy.2
    simp only [Fin.sum_univ_two] at hs
    linarith [hy.1 0]
  have hw : payoff values xDominant y=1 := by
    have hleft : y 0<(1/2:ℝ) := by linarith
    have hright : y 1<(1/2:ℝ) := by linarith
    have hshare0 : share (xDominant 0) (y 0)=1 := by
      change y 0<xDominant 0 at hleft
      simp only [share,hleft,ite_true]
    have hshare1 : share (xDominant 1) (y 1)=1 := by
      change y 1<xDominant 1 at hright
      simp only [share,hright,ite_true]
    norm_num [payoff,Fin.sum_univ_two,values,hshare0,hshare1]
  exact ⟨hw,by linarith [payoff_constant_sum values xDominant y]⟩

theorem dominant_is_pure_equilibrium (y : Allocation 2)
    (hy : Feasible (1/3:ℝ) y) :
    Feasible 1 xDominant ∧
    (∀ x : Allocation 2,Feasible 1 x →
      payoff values x y≤payoff values xDominant y) ∧
    (∀ z : Allocation 2,Feasible (1/3:ℝ) z →
      payoff values z xDominant≤payoff values y xDominant) := by
  have hpay:=dominant_wins y hy
  refine ⟨dominant_feasible,?_,?_⟩
  · intro x _
    rw [hpay.1]
    exact payoff_le_one values x y
  · intro z hz
    rw [hpay.2,(dominant_wins z hz).2]

end Blotto.GeneralPaperSecurityCounterexample
