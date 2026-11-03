import Blotto.PlayerSpecificSupport

/-! Exact player-specific Nash for the two constructed whole laws. Each
player's own values enter its affine best-response bound. No constant-sum
identity with a common value vector is used. -/
namespace Blotto.PlayerSpecificEquilibrium
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def intercept {n : ℕ} (v : Values n) (p : Fin n → ℝ) : ℝ :=
  ∑ j,v.weight j*(1-p j)

theorem scalar_equality (L p s : ℝ) (hL : 0<L) (hp : 0≤p) (hp1 : p≤1)
    (hs : s∈Icc 0 L) (hn : p=1 ∨ s≠0) :
    (∫ t,share s t ∂zeroUniformLaw L p)=1-p+p*(s/L) := by
  rw [zeroUniform_integral_share L hL hp hp1,min_eq_left hs.2,max_eq_left hs.1]
  rcases hn with rfl | hn
  · ring
  · have hpos : 0<s := lt_of_le_of_ne hs.1 (Ne.symm hn)
    simp only [share,hpos,ite_true]
    ring

theorem pure_upper {n : ℕ} (v : Values n) (B sigma : ℝ) (ν : Mixed n)
    (L p : Fin n → ℝ) (hL : ∀ j,0<L j) (hp : ∀ j,0≤p j ∧ p j≤1)
    (hSlope : ∀ j,v.weight j*p j/L j=sigma) (hSigma : 0≤sigma)
    (hMarginal : ∀ j,(marginal ν j : Measure ℝ)=zeroUniformLaw (L j) (p j))
    (x : Allocation n) (hx : Feasible B x) :
    purePayoff v x ν≤ intercept v p+sigma*B := by
  rw [purePayoff_marginal_integrals]
  calc
    _ ≤ ∑ j,(v.weight j*(1-p j)+sigma*x j) := by
      apply Finset.sum_le_sum
      intro j _
      rw [hMarginal j]
      calc
        _ ≤ v.weight j*(1-p j+p j*(x j/L j)) :=
          mul_le_mul_of_nonneg_left (zeroUniform_share_upper (L j) (hL j) (hp j).1 (hp j).2 (hx.1 j)) (v.positive j).le
        _ = v.weight j*(1-p j)+(v.weight j*p j/L j)*x j := by ring
        _ = _ := by rw [hSlope j]
    _ = intercept v p+sigma*(∑ j,x j) := by rw [Finset.sum_add_distrib,← Finset.mul_sum]; rfl
    _ ≤ intercept v p+sigma*B := add_le_add le_rfl (mul_le_mul_of_nonneg_left hx.2 hSigma)

theorem pure_equality {n : ℕ} (v : Values n) (B sigma : ℝ) (ν : Mixed n)
    (L p : Fin n → ℝ) (hL : ∀ j,0<L j) (hp : ∀ j,0≤p j ∧ p j≤1)
    (hSlope : ∀ j,v.weight j*p j/L j=sigma)
    (hMarginal : ∀ j,(marginal ν j : Measure ℝ)=zeroUniformLaw (L j) (p j))
    (x : Allocation n) (hx : FullBudget B x)
    (hOwn : ∀ j,x j∈Icc 0 (L j) ∧ (p j=1 ∨ x j≠0)) :
    purePayoff v x ν=intercept v p+sigma*B := by
  rw [purePayoff_marginal_integrals]
  calc
    _ = ∑ j,(v.weight j*(1-p j)+sigma*x j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hMarginal j,scalar_equality (L j) (p j) (x j) (hL j) (hp j).1 (hp j).2 (hOwn j).1 (hOwn j).2]
      calc
        _ = v.weight j*(1-p j)+(v.weight j*p j/L j)*x j := by ring
        _ = _ := by rw [hSlope j]
    _ = intercept v p+sigma*(∑ j,x j) := by rw [Finset.sum_add_distrib,← Finset.mul_sum]; rfl
    _ = _ := by rw [hx.2]

theorem affine_equilibrium {n : ℕ} (v : Values n) (B sigma : ℝ) (μ ν : Mixed n)
    (L p : Fin n → ℝ) (hB : 0≤B) (hL : ∀ j,0<L j) (hp : ∀ j,0≤p j ∧ p j≤1)
    (hSlope : ∀ j,v.weight j*p j/L j=sigma) (hSigma : 0≤sigma)
    (hMarginal : ∀ j,(marginal ν j : Measure ℝ)=zeroUniformLaw (L j) (p j))
    (hBudget : ∀ᵐ x ∂(μ : Measure (Allocation n)),FullBudget B x)
    (hOwn : ∀ᵐ x ∂(μ : Measure (Allocation n)),∀ j,x j∈Icc 0 (L j) ∧ (p j=1 ∨ x j≠0)) :
    regret v B μ ν=0 ∧ expected v μ ν=intercept v p+sigma*B := by
  have he : expected v μ ν=intercept v p+sigma*B := by
    rw [expected_iterated]
    calc
      _ = ∫ _x : Allocation n,(intercept v p+sigma*B) ∂(μ : Measure (Allocation n)) := by
        apply integral_congr_ae
        filter_upwards [hBudget,hOwn] with x hx ho
        exact pure_equality v B sigma ν L p hL hp hSlope hMarginal x hx ho
      _ = _ := by simp
  have hs := security_le v hB ν (fun x hx => pure_upper v B sigma ν L p hL hp hSlope hSigma hMarginal x hx)
  have hSupport : Supported B μ := hBudget.mono (fun _ hx => ⟨hx.1,hx.2.le⟩)
  refine ⟨le_antisymm ?_ (regret_nonneg v μ ν hSupport),he⟩
  rw [regret,he]
  exact sub_nonpos.mpr hs

theorem exact_nash {n : ℕ} (i : PlayerSpecificInput n) :
    regret i.valuesA 1 i.lawA i.lawB=0 ∧ regret i.valuesB i.budget i.lawB i.lawA=0 ∧
      expected i.valuesA i.lawA i.lawB=intercept i.valuesA i.probB+i.scale ∧
      expected i.valuesB i.lawB i.lawA=intercept i.valuesB i.probA+(i.scale/i.gamma)*i.budget := by
  have hA := affine_equilibrium i.valuesA 1 i.scale i.lawA i.lawB i.length i.probB (by norm_num)
    i.length_pos (fun j => ⟨(i.probB_bounds j).1.le,(i.probB_bounds j).2⟩)
    (fun j => PlayerSpecificMarginals.slopeA (i.valuesA.positive j) (i.valuesB.positive j) i.gamma_pos)
    i.scale_pos.le i.lawB_marginal i.lawA_budget (PlayerSpecificSupport.lawA i)
  have hB := affine_equilibrium i.valuesB i.budget (i.scale/i.gamma) i.lawB i.lawA i.length i.probA i.budget_pos.le
    i.length_pos (fun j => ⟨(i.probA_bounds j).1.le,(i.probA_bounds j).2⟩)
    (fun j => PlayerSpecificMarginals.slopeB (i.valuesA.positive j) (i.valuesB.positive j) i.gamma_pos i.scale_pos)
    (div_nonneg i.scale_pos.le i.gamma_pos.le) i.lawA_marginal i.lawB_budget (PlayerSpecificSupport.lawB i)
  exact ⟨hA.1,hB.1,by simpa only [mul_one] using hA.2,hB.2⟩

end Blotto.PlayerSpecificEquilibrium
