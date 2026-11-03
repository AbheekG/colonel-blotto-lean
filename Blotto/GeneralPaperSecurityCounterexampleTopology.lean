import Blotto.GeneralPaperSecurityCounterexampleMixed
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Analysis.SpecificLimits.Basic

/-! The nearby dominating pure allocations converge as Dirac laws in
the mixed-strategy weak topology. This supplies the actual neighborhood
witness behind the security counterexample. -/
namespace Blotto.GeneralPaperSecurityCounterexampleTopology
open MeasureTheory Filter GeneralPaperSecurityCounterexample
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 2500000

private noncomputable def t (n : ℕ) : ℝ := (1/4:ℝ)*(1/((n:ℝ)+1))

private theorem t_valid (n : ℕ) : 0<t n ∧ t n<1/3 := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hd : 0<(n:ℝ)+1 := by linarith
  have hdiv : 0<1/((n:ℝ)+1) := by positivity
  have hle : 1/((n:ℝ)+1)≤1 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  dsimp only [t]
  constructor
  · positivity
  · nlinarith

private theorem t_tendsto : Tendsto t atTop (𝓝 (0:ℝ)) := by
  have h : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Tendsto (fun _ : ℕ => (1/4:ℝ)) atTop (𝓝 (1/4:ℝ)) :=
    tendsto_const_nhds
  change Tendsto (fun n : ℕ => (1/4:ℝ)*(1/((n:ℝ)+1))) atTop (𝓝 (0:ℝ))
  simpa only [mul_zero] using hc.mul h

private theorem move_zero : xMove 0=xStar := by
  funext j
  fin_cases j <;> norm_num [xMove,xStar]

private theorem continuous_move : Continuous xMove := by
  apply continuous_pi
  intro j
  fin_cases j
  · change Continuous (fun z : ℝ => (1/3:ℝ)+z)
    fun_prop
  · change Continuous (fun z : ℝ => (2/3:ℝ)-z)
    fun_prop

theorem weak_dirac_convergence :
    Tendsto (fun n : ℕ => diracProba (xMove (t n))) atTop
      (𝓝 (diracProba xStar)) := by
  have h : Tendsto (fun z : ℝ => diracProba (xMove z)) (𝓝 (0:ℝ))
      (𝓝 (diracProba (xMove 0))) :=
    (continuous_diracProba.comp continuous_move).continuousAt.tendsto
  rw [move_zero] at h
  exact h.comp t_tendsto

theorem every_weak_neighborhood_has_unbeatable_A
    (U : Set (Mixed 2)) (hU : U∈𝓝 (diracProba xStar)) :
    ∃ s : ℝ,0<s ∧ s<1/3 ∧ diracProba (xMove s)∈U ∧
      ∀ nu : Mixed 2,Supported (1/3:ℝ) nu →
        (∫ y, payoff values y (xMove s) ∂(nu : Measure (Allocation 2)))=0 := by
  obtain ⟨n,hn⟩ := (weak_dirac_convergence.eventually hU).exists
  exact ⟨t n,(t_valid n).1,(t_valid n).2,hn,
    fun nu hnu => GeneralPaperSecurityCounterexampleMixed.every_mixed_B_loses
      (t n) (t_valid n) nu hnu⟩

theorem mixed_B_payoff_against_move (s : ℝ) (hs : 0<s ∧ s<1/3)
    (nu : Mixed 2) (hnu : Supported (1/3:ℝ) nu) :
    expected values nu (diracProba (xMove s))=0 := by
  rw [expected_iterated]
  have hdirac (y : Allocation 2) :
      purePayoff values y (diracProba (xMove s))=payoff values y (xMove s) := by
    simp [purePayoff,diracProba]
  simp_rw [hdirac]
  exact GeneralPaperSecurityCounterexampleMixed.every_mixed_B_loses s hs nu hnu

theorem no_mixed_B_positive_security_near_star
    (U : Set (Mixed 2)) (hU : U∈𝓝 (diracProba xStar)) :
    ∃ mu : Mixed 2,mu∈U ∧
      ∀ nu : Mixed 2,Supported (1/3:ℝ) nu → expected values nu mu=0 := by
  obtain ⟨s,hs,hs',hmem,_⟩:=every_weak_neighborhood_has_unbeatable_A U hU
  exact ⟨diracProba (xMove s),hmem,
    fun nu hnu => mixed_B_payoff_against_move s ⟨hs,hs'⟩ nu hnu⟩

theorem mixed_star_payoffs :
    expected values (diracProba xStar) (diracProba yStar)=3/4 ∧
      expected values (diracProba yStar) (diracProba xStar)=1/4 := by
  constructor
  · rw [expected_iterated]
    simpa [purePayoff,diracProba] using (at_star).1
  · rw [expected_iterated]
    simpa [purePayoff,diracProba] using (at_star).2

theorem no_mixed_B_positive_guarantee (r : ℝ) (hr : 0≤r) :
    ¬ ∃ nu : Mixed 2,Supported (1/3:ℝ) nu ∧
      ∃ U : Set (Mixed 2),U∈𝓝 (diracProba xStar) ∧
        ∀ mu∈U,r<expected values nu mu := by
  rintro ⟨nu,hnu,U,hU,hguarantee⟩
  obtain ⟨mu,hmu,hzero⟩:=no_mixed_B_positive_security_near_star U hU
  have hpositive:=hguarantee mu hmu
  rw [hzero nu hnu] at hpositive
  linarith

theorem A_mixed_payoff_le_one (mu nu : Mixed 2) :
    expected values mu nu≤1 := by
  let rho:=((mu : Measure (Allocation 2)).prod (nu : Measure (Allocation 2)))
  have hc : Integrable (fun _ : Allocation 2 × Allocation 2 => (1:ℝ)) rho :=
    integrable_const _
  have hm:=integral_mono (integrable_payoff values rho) hc
    (fun z => payoff_le_one values z.1 z.2)
  unfold expected
  simpa [rho] using hm

theorem security_obstructions :
    (∀ mu nu : Mixed 2,expected values mu nu≤1) ∧
    (¬ ∃ nu : Mixed 2,Supported (1/3:ℝ) nu ∧
      ∃ U : Set (Mixed 2),U∈𝓝 (diracProba xStar) ∧
        ∀ mu∈U,(0:ℝ)<expected values nu mu) ∧
    (¬ ∃ nu : Mixed 2,Supported (1/3:ℝ) nu ∧
      ∃ U : Set (Mixed 2),U∈𝓝 (diracProba xStar) ∧
        ∀ mu∈U,(1/8:ℝ)<expected values nu mu) := by
  exact ⟨A_mixed_payoff_le_one,no_mixed_B_positive_guarantee 0 (by norm_num),
    no_mixed_B_positive_guarantee (1/8) (by norm_num)⟩

end Blotto.GeneralPaperSecurityCounterexampleTopology
