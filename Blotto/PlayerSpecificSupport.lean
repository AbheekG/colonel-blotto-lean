import Blotto.PlayerSpecificInput
import Blotto.UniformSupport

/-! The two atoms at zero are complementary. Consequently every own-law
coordinate lies in the interval on which the opposing marginal's affine
payoff bound is attained, except on a proved null set. -/
namespace Blotto.PlayerSpecificSupport
open MeasureTheory Set
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem zeroUniform_box (L p : ℝ) (hL : 0≤L) :
    ∀ᵐ s ∂zeroUniformLaw L p,s∈Icc 0 L := by
  rw [zeroUniformLaw,ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (by simpa using hL) _,
    Measure.ae_smul_measure (uniformLaw_supported L) _⟩

theorem zeroUniform_one_nonzero (L : ℝ) :
    ∀ᵐ s ∂zeroUniformLaw L 1,s≠0 := by
  simp only [zeroUniformLaw,sub_self,ENNReal.ofReal_zero,zero_smul,zero_add,
    ENNReal.ofReal_one,one_smul]
  rw [ae_iff]
  simpa using uniform_singleton L 0

theorem compatible (L p q : ℝ) (hL : 0≤L) (hComp : (1-p)*(1-q)=0) :
    ∀ᵐ s ∂zeroUniformLaw L p,s∈Icc 0 L ∧ (q=1 ∨ s≠0) := by
  by_cases hq : q=1
  · exact (zeroUniform_box L p hL).mono (fun s hs => ⟨hs,Or.inl hq⟩)
  · have hp : p=1 := by
      rcases mul_eq_zero.mp hComp with h | h
      · linarith
      · exact (hq (by linarith)).elim
    rw [hp]
    filter_upwards [zeroUniform_box L 1 hL,zeroUniform_one_nonzero L] with s hs hn
    exact ⟨hs,Or.inr hn⟩

theorem marginal_compatible {n : ℕ} (μ : Mixed n) (j : Fin n) (L p q : ℝ)
    (hL : 0≤L) (hComp : (1-p)*(1-q)=0)
    (hMarginal : (marginal μ j : Measure ℝ)=zeroUniformLaw L p) :
    ∀ᵐ x ∂(μ : Measure (Allocation n)),x j∈Icc 0 L ∧ (q=1 ∨ x j≠0) := by
  have hm := compatible L p q hL hComp
  rw [← hMarginal] at hm
  change ∀ᵐ s ∂Measure.map (fun x : Allocation n => x j) (μ : Measure (Allocation n)),
    s∈Icc 0 L ∧ (q=1 ∨ s≠0) at hm
  exact (ae_map_iff (measurable_pi_apply j).aemeasurable (by measurability)).mp hm

theorem lawA {n : ℕ} (i : PlayerSpecificInput n) :
    ∀ᵐ x ∂(i.lawA : Measure (Allocation n)),∀ j,x j∈Icc 0 (i.length j) ∧ (i.probB j=1 ∨ x j≠0) := by
  apply ae_all_iff.mpr
  intro j
  exact marginal_compatible i.lawA j (i.length j) (i.probA j) (i.probB j) (i.length_pos j).le
    (PlayerSpecificMarginals.complementary_atoms (i.valuesA.positive j) (i.valuesB.positive j) i.gamma_pos)
    (i.lawA_marginal j)

theorem lawB {n : ℕ} (i : PlayerSpecificInput n) :
    ∀ᵐ x ∂(i.lawB : Measure (Allocation n)),∀ j,x j∈Icc 0 (i.length j) ∧ (i.probA j=1 ∨ x j≠0) := by
  apply ae_all_iff.mpr
  intro j
  apply marginal_compatible i.lawB j (i.length j) (i.probB j) (i.probA j) (i.length_pos j).le _ (i.lawB_marginal j)
  rw [mul_comm]
  exact PlayerSpecificMarginals.complementary_atoms (i.valuesA.positive j) (i.valuesB.positive j) i.gamma_pos

end Blotto.PlayerSpecificSupport
