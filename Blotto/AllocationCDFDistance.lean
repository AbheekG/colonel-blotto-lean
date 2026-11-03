import Blotto.MidpointSegments
import Blotto.Translate
import Blotto.CoordinatePermutation
import Blotto.BinaryMixture

/-! Composition of marginal CDF errors and third-coordinate translations. -/

namespace Blotto
open MeasureTheory

namespace CDFClose

theorem symm {n : ℕ} {μ ν : Mixed n} {δ : ℝ} (h : CDFClose μ ν δ) : CDFClose ν μ δ := by
  intro j z
  rw [abs_sub_comm]
  exact h j z

theorem triangle {n : ℕ} {μ ν τ : Mixed n} {δ η : ℝ} (h : CDFClose μ ν δ) (g : CDFClose ν τ η) :
    CDFClose μ τ (δ + η) := by
  intro j z
  exact (abs_sub_le _ _ _).trans (add_le_add (h j z) (g j z))

theorem mono {n : ℕ} {μ ν : Mixed n} {δ η : ℝ} (h : CDFClose μ ν δ) (he : δ ≤ η) : CDFClose μ ν η :=
  fun j z => (h j z).trans he

end CDFClose

namespace RealCDFClose

theorem translate {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) (s : ℝ) :
    RealCDFClose (ρ.map (fun x => x + s)) (σ.map (fun x => x + s)) δ := by
  have hf : affineLine s (s + 1) = fun x => x + s := by funext x; unfold affineLine; ring
  have he := h.affine s (s + 1)
  rw [hf] at he
  exact he

end RealCDFClose

theorem shiftedLaw_CDFClose {μ ν : Mixed 3} {δ : ℝ} (h : CDFClose μ ν δ) (s : ℝ) :
    CDFClose (shiftedLaw s μ) (shiftedLaw s ν) δ := by
  intro j z
  unfold closedCDF
  fin_cases j
  · change |(marginal (shiftedLaw s μ) 0 : Measure ℝ).real _ - (marginal (shiftedLaw s ν) 0 : Measure ℝ).real _| ≤ _
    rw [shiftedLaw_marginal_zero, shiftedLaw_marginal_zero]
    exact h 0 z
  · change |(marginal (shiftedLaw s μ) 1 : Measure ℝ).real _ - (marginal (shiftedLaw s ν) 1 : Measure ℝ).real _| ≤ _
    rw [shiftedLaw_marginal_one, shiftedLaw_marginal_one]
    exact h 1 z
  · change |(marginal (shiftedLaw s μ) 2 : Measure ℝ).real _ - (marginal (shiftedLaw s ν) 2 : Measure ℝ).real _| ≤ _
    rw [shiftedLaw_marginal_two, shiftedLaw_marginal_two]
    have he : RealCDFClose (marginal μ 2) (marginal ν 2) δ := fun t => h 2 t
    exact he.translate s z

theorem binaryLaw_CDFClose {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    {μ μ' ν ν' : Mixed n} {δ : ℝ} (hμ : CDFClose μ μ' δ) (hν : CDFClose ν ν' δ) :
    CDFClose (binaryLaw p hp μ ν) (binaryLaw p hp μ' ν') δ := by
  apply probabilityMixture_CDFClose
  intro j
  fin_cases j
  · exact hμ
  · exact hν

theorem permuteLaw_CDFClose {n : ℕ} {μ ν : Mixed n} {δ : ℝ} (h : CDFClose μ ν δ)
    (π : Equiv.Perm (Fin n)) : CDFClose (permuteLaw π μ) (permuteLaw π ν) δ := by
  intro j z
  unfold closedCDF
  rw [permuteLaw_marginal, permuteLaw_marginal]
  exact h (π j) z

theorem swapLaw_CDFClose {μ ν : Mixed 3} {δ : ℝ} (h : CDFClose μ ν δ) : CDFClose (swapLaw μ) (swapLaw ν) δ := by
  intro j z
  unfold closedCDF
  rw [swapLaw_marginal, swapLaw_marginal]
  exact h (swapIndex j) z

end Blotto
