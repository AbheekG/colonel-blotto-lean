import Blotto.PureBoundaryEquilibria
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Compactness of the actual canonical at-most-budget law domain in
the weak topology. The compact set contains arbitrary whole-allocation
probability laws, rather than a grid or a finite-support restriction. -/

namespace Blotto.CompactFeasibleLaws
open MeasureTheory Set Filter
open scoped Topology BigOperators

theorem feasible_closed {n : ℕ} (budget : ℝ) :
    IsClosed {row : Allocation n | Feasible budget row} := by
  have hPositive : IsClosed {row : Allocation n | ∀ j, 0 ≤ row j} := by
    have he : {row : Allocation n | ∀ j, 0 ≤ row j} =
        ⋂ j : Fin n, {row | 0 ≤ row j} := by ext row; simp
    rw [he]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have hSum : Continuous (fun row : Allocation n => ∑ j, row j) :=
    continuous_finsetSum _ fun j _ => continuous_apply j
  exact hPositive.inter (isClosed_le hSum continuous_const)

theorem feasible_compact {n : ℕ} (budget : ℝ) :
    IsCompact {row : Allocation n | Feasible budget row} := by
  have hBox : IsCompact {row : Allocation n | ∀ j, row j ∈ Icc 0 budget} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  apply hBox.of_isClosed_subset (feasible_closed budget)
  intro row hRow j
  exact ⟨hRow.1 j,PureBoundaryEquilibria.feasible_coordinate_le hRow j⟩

theorem supported_iff_complement_zero {n : ℕ} (budget : ℝ) (law : Mixed n) :
    Supported budget law ↔ law {row : Allocation n | Feasible budget row}ᶜ = 0 := by
  unfold Supported
  rw [ae_iff]
  change (law : Measure (Allocation n)) {row : Allocation n | Feasible budget row}ᶜ = 0 ↔
    ((law : Measure (Allocation n)) {row : Allocation n | Feasible budget row}ᶜ).toNNReal = 0
  simp [ENNReal.toNNReal_eq_zero_iff,measure_ne_top]

theorem supported_compact {n : ℕ} (budget : ℝ) :
    IsCompact {law : Mixed n | Supported budget law} := by
  have hCompact := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ : ℕ => (0 : NNReal))
    (K := fun _ : ℕ => {row : Allocation n | Feasible budget row})
    tendsto_const_nhds (fun _ => feasible_compact budget)
    (Or.inr (fun _ _ _ => Subset.rfl))
  have hSets : {law : Mixed n | ∀ _ : ℕ,
      law {row : Allocation n | Feasible budget row}ᶜ ≤ (0 : NNReal)} =
      {law : Mixed n | Supported budget law} := by
    ext law
    simp [supported_iff_complement_zero]
  rwa [hSets] at hCompact

end Blotto.CompactFeasibleLaws
