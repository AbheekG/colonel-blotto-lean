import Blotto.ReflectAppend
import Blotto.ProportionalCDF
import Blotto.ThreeDyadicCoupling

/-! Reflection with an appended zero and proportional splitting of a merged
pair preserve CDF error. Both are maps of an entire allocation law. -/

namespace Blotto
open MeasureTheory

namespace RealCDFClose

theorem reflect {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) (L : ℝ) :
    RealCDFClose (ρ.map (fun x => L - x)) (σ.map (fun x => L - x)) δ := by
  have hf : affineLine L (L - 1) = fun x => L - x := by funext x; unfold affineLine; ring
  have he := h.affine L (L - 1)
  rw [hf] at he
  exact he

end RealCDFClose

theorem reflectedLaw_CDFClose (L : Allocation 3) {μ ν : Mixed 3} {δ : ℝ} (h : CDFClose μ ν δ) :
    CDFClose (reflectedLaw L μ) (reflectedLaw L ν) δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (h 0 0)
  intro j z
  unfold closedCDF
  rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
  · rw [reflectedLaw_marginal_first, reflectedLaw_marginal_first]
    have hc : RealCDFClose (marginal μ k) (marginal ν k) δ := fun t => h k t
    exact hc.reflect (L k) z
  · change |(marginal (reflectedLaw L μ) 3 : Measure ℝ).real _ - (marginal (reflectedLaw L ν) 3 : Measure ℝ).real _| ≤ _
    rw [reflectedLaw_marginal_last, reflectedLaw_marginal_last]
    simpa only [sub_self, abs_zero] using hδ

theorem splitLaw_CDFClose (a d : ℝ) {μ ν : Mixed 3} {δ : ℝ} (h : CDFClose μ ν δ) :
    CDFClose (splitLaw a d μ) (splitLaw a d ν) δ := by
  have hμ := splitLaw_marginals a d μ
  have hν := splitLaw_marginals a d ν
  have hc : RealCDFClose (marginal μ 0) (marginal ν 0) δ := fun t => h 0 t
  intro j z
  unfold closedCDF
  fin_cases j
  · change |(marginal (splitLaw a d μ) 0 : Measure ℝ).real _ - (marginal (splitLaw a d ν) 0 : Measure ℝ).real _| ≤ _
    rw [hμ.1, hν.1]
    exact hc.scale (a / (a + d)) z
  · change |(marginal (splitLaw a d μ) 1 : Measure ℝ).real _ - (marginal (splitLaw a d ν) 1 : Measure ℝ).real _| ≤ _
    rw [hμ.2.1, hν.2.1]
    exact hc.scale (d / (a + d)) z
  · change |(marginal (splitLaw a d μ) 2 : Measure ℝ).real _ - (marginal (splitLaw a d ν) 2 : Measure ℝ).real _| ≤ _
    rw [hμ.2.2.1, hν.2.2.1]
    exact h 1 z
  · change |(marginal (splitLaw a d μ) 3 : Measure ℝ).real _ - (marginal (splitLaw a d ν) 3 : Measure ℝ).real _| ≤ _
    rw [hμ.2.2.2, hν.2.2.2]
    exact h 2 z

namespace MergeFourInput

noncomputable def dyadicLaw (i : MergeFourInput) (K : ℕ) : Mixed 4 := splitLaw i.l0 i.l1 (i.childSpec.dyadicLaw K)

theorem dyadicLaw_CDF_error (i : MergeFourInput) (K : ℕ) :
    CDFClose (i.dyadicLaw K) i.law (1 / (2 * (2 : ℝ) ^ K)) :=
  splitLaw_CDFClose _ _ (i.childSpec.dyadicLaw_CDF_error K)

theorem dyadicLaw_fullBudget (i : MergeFourInput) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 4)), FullBudget i.B x :=
  splitLaw_fullBudget i.l0_pos i.l1_pos _ (i.childSpec.dyadicLaw_fullBudget K)

end MergeFourInput
end Blotto
