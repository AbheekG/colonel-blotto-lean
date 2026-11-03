import Blotto.GeneralPaperRoundedValueSourceInput

/-! L1 perturbation of canonical half-tie payoffs, arbitrary independent
whole-allocation laws and the supremum over every feasible continuous
deviation. Supports and hard budgets do not depend on value weights. -/
namespace Blotto.GeneralPaperValuePerturbation
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

noncomputable def distance {n : ℕ} (v w : Values n) : ℝ := ∑ j,|v.weight j-w.weight j|

theorem nonnegative {n : ℕ} (v w : Values n) : 0≤distance v w := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem symmetric {n : ℕ} (v w : Values n) : distance v w=distance w v := by
  unfold distance
  exact Finset.sum_congr rfl (fun j _ => abs_sub_comm _ _)

theorem payoff_abs {n : ℕ} (v w : Values n) (x y : Allocation n) :
    |payoff v x y-payoff w x y|≤distance v w := by
  rw [payoff,payoff,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [←sub_mul,abs_mul,abs_of_nonneg (share_nonneg _ _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (share_le_one _ _)

theorem pure_le {n : ℕ} (v w : Values n) (x : Allocation n) (ν : Mixed n) :
    purePayoff v x ν≤purePayoff w x ν+distance v w := by
  have hw := integrable_payoff_right w x ν
  have h := integral_mono (integrable_payoff_right v x ν) (hw.add (integrable_const (distance v w)))
    (fun y => by
      change payoff v x y ≤ payoff w x y+distance v w
      have hp := (abs_le.mp (payoff_abs v w x y)).2
      linarith only [hp])
  simpa [purePayoff,integral_add hw (integrable_const (distance v w))] using h

theorem pure_abs {n : ℕ} (v w : Values n) (x : Allocation n) (ν : Mixed n) :
    |purePayoff v x ν-purePayoff w x ν|≤distance v w := by
  have h0 := pure_le v w x ν
  have h1 := pure_le w v x ν
  rw [symmetric w v] at h1
  exact abs_le.mpr ⟨by linarith only [h1],by linarith only [h0]⟩

theorem expected_le {n : ℕ} (v w : Values n) (μ ν : Mixed n) :
    expected v μ ν≤expected w μ ν+distance v w := by
  let ρ := (μ : Measure (Allocation n)).prod (ν : Measure (Allocation n))
  have hw := integrable_payoff w ρ
  have h := integral_mono (integrable_payoff v ρ) (hw.add (integrable_const (distance v w)))
    (fun z => by
      change payoff v z.1 z.2 ≤ payoff w z.1 z.2+distance v w
      have hp := (abs_le.mp (payoff_abs v w z.1 z.2)).2
      linarith only [hp])
  simpa [expected,ρ,integral_add hw (integrable_const (distance v w))] using h

theorem expected_abs {n : ℕ} (v w : Values n) (μ ν : Mixed n) :
    |expected v μ ν-expected w μ ν|≤distance v w := by
  have h0 := expected_le v w μ ν
  have h1 := expected_le w v μ ν
  rw [symmetric w v] at h1
  exact abs_le.mpr ⟨by linarith only [h1],by linarith only [h0]⟩

theorem security_le_shift {n : ℕ} (v w : Values n) (B : ℝ) (hB : 0≤B) (ν : Mixed n) :
    security v B ν≤security w B ν+distance v w := by
  apply security_le v hB
  intro x hx
  have h0 := pure_le v w x ν
  have h1 := purePayoff_le_security w hx ν
  linarith only [h0,h1]

theorem security_abs {n : ℕ} (v w : Values n) (B : ℝ) (hB : 0≤B) (ν : Mixed n) :
    |security v B ν-security w B ν|≤distance v w := by
  have h0 := security_le_shift v w B hB ν
  have h1 := security_le_shift w v B hB ν
  rw [symmetric w v] at h1
  exact abs_le.mpr ⟨by linarith only [h1],by linarith only [h0]⟩

theorem regret_le_shift {n : ℕ} (v w : Values n) (B : ℝ) (hB : 0≤B) (μ ν : Mixed n) :
    regret v B μ ν≤regret w B μ ν+2*distance v w := by
  have h0 := security_le_shift v w B hB ν
  have h1 := expected_le w v μ ν
  rw [symmetric w v] at h1
  unfold regret
  linarith only [h0,h1]

theorem regret_abs {n : ℕ} (v w : Values n) (B : ℝ) (hB : 0≤B) (μ ν : Mixed n) :
    |regret v B μ ν-regret w B μ ν|≤2*distance v w := by
  have h0 := regret_le_shift v w B hB μ ν
  have h1 := regret_le_shift w v B hB μ ν
  rw [symmetric w v] at h1
  exact abs_le.mpr ⟨by linarith only [h1],by linarith only [h0]⟩

theorem transfer_regrets {n : ℕ} (v w : Values n) (A B ε δ : ℝ) (hA : 0≤A) (hB : 0≤B)
    (μ ν : Mixed n) (hδ : distance v w≤δ) (hμ : regret w A μ ν≤ε) (hν : regret w B ν μ≤ε) :
    regret v A μ ν≤ε+2*δ ∧ regret v B ν μ≤ε+2*δ := by
  have h0 := regret_le_shift v w A hA μ ν
  have h1 := regret_le_shift v w B hB ν μ
  constructor <;> linarith only [h0,h1,hδ,hμ,hν]

end Blotto.GeneralPaperValuePerturbation
