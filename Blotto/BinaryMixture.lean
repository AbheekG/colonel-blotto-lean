import Blotto.FiniteMixture

/-! Exact binary mixtures of whole-allocation laws. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

noncomputable def binaryLaw {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (μ ν : Mixed n) : Mixed n :=
  probabilityMixture ![p, 1 - p] ![μ, ν]
    (by intro i; fin_cases i; exact hp.1; exact sub_nonneg.mpr hp.2)
    (by simp [Fin.sum_univ_succ])

theorem binaryLaw_measure {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (μ ν : Mixed n) :
    (binaryLaw p hp μ ν : Measure (Allocation n)) =
      ENNReal.ofReal p • (μ : Measure (Allocation n)) +
        ENNReal.ofReal (1 - p) • (ν : Measure (Allocation n)) := by
  simp [binaryLaw, probabilityMixture, mixtureMeasure, Measure.sum_fintype, Fin.sum_univ_succ]

theorem binaryLaw_fullBudget {n : ℕ} {B : ℝ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (μ ν : Mixed n)
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation n)), FullBudget B x)
    (hν : ∀ᵐ x ∂(ν : Measure (Allocation n)), FullBudget B x) :
    ∀ᵐ x ∂(binaryLaw p hp μ ν : Measure (Allocation n)), FullBudget B x := by
  apply probabilityMixture_ae
  intro i
  fin_cases i
  · exact hμ
  · exact hν

theorem binaryLaw_marginal {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (μ ν : Mixed n) (j : Fin n) :
    (marginal (binaryLaw p hp μ ν) j : Measure ℝ) =
      ENNReal.ofReal p • (marginal μ j : Measure ℝ) +
        ENNReal.ofReal (1 - p) • (marginal ν j : Measure ℝ) := by
  rw [binaryLaw, probabilityMixture_marginal, Measure.sum_fintype]
  simp [Fin.sum_univ_succ]

theorem binaryLaw_marginal_common {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (μ ν : Mixed n) (j : Fin n) (ρ : Measure ℝ)
    (hμ : (marginal μ j : Measure ℝ) = ρ) (hν : (marginal ν j : Measure ℝ) = ρ) :
    (marginal (binaryLaw p hp μ ν) j : Measure ℝ) = ρ := by
  rw [binaryLaw_marginal, hμ, hν, ← add_smul,
    ← ENNReal.ofReal_add hp.1 (sub_nonneg.mpr hp.2)]
  simp

end Blotto
