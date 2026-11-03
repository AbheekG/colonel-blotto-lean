import Blotto.FiniteMixture

/-! Actual finite uniform laws on real points, with event probabilities and
expectations expressed as finite sums. No fair-bit implementation is assumed. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def realPointLaw (x : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac x, inferInstance⟩

theorem uniformWeights_sum {N : ℕ} (hN : 0 < N) :
    (∑ _ : Fin N, (1 / (N : ℝ))) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

noncomputable def finiteUniformPoints {N : ℕ} (hN : 0 < N) (point : Fin N → ℝ) : ProbabilityMeasure ℝ :=
  probabilityMixture (fun _ => 1 / (N : ℝ)) (fun i => realPointLaw (point i))
    (fun _ => by positivity) (uniformWeights_sum hN)

theorem finiteUniformPoints_event {N : ℕ} (hN : 0 < N) (point : Fin N → ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (finiteUniformPoints hN point : Measure ℝ).real A =
      (∑ i : Fin N, if point i ∈ A then (1 : ℝ) else 0) / N := by
  classical
  change (Measure.sum (fun i : Fin N => ENNReal.ofReal (1 / (N : ℝ)) • Measure.dirac (point i))).real A = _
  unfold Measure.real
  rw [Measure.sum_apply _ hA, tsum_fintype,
    ENNReal.toReal_sum (fun i _ => by
      rw [Measure.smul_apply]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ A))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : point i ∈ A
  · simp [Measure.smul_apply, Measure.dirac_apply' _ hA, hi]
  · simp [Measure.smul_apply, Measure.dirac_apply' _ hA, hi]

theorem finiteUniformPoints_supported {N : ℕ} (hN : 0 < N) (point : Fin N → ℝ)
    {P : ℝ → Prop} (hP : ∀ i, P (point i)) :
    ∀ᵐ x ∂(finiteUniformPoints hN point : Measure ℝ), P x := by
  apply probabilityMixture_ae
  intro i
  change ∀ᵐ x ∂Measure.dirac (point i), P x
  rw [ae_dirac_eq]
  exact hP i

end Blotto
