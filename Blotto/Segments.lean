import Blotto.UniformInterval
import Blotto.ThreeGeometry

/-! A segment draw is a probability law on a whole allocation vector.
Its marginals are actual push-forwards; feasibility is pointwise and almost sure. -/

namespace Blotto

open MeasureTheory Set Filter
open scoped BigOperators

theorem measurable_segmentPoint {n : ℕ} (P Q : Allocation n) :
    Measurable (segmentPoint P Q) := by
  apply Measurable.of_eval
  intro j
  exact measurable_affineLine (P j) (Q j)

noncomputable def segmentLaw {n : ℕ} (P Q : Allocation n) : Mixed n :=
  unitUniform.map (segmentPoint P Q)

theorem segmentLaw_marginal {n : ℕ} (P Q : Allocation n) (j : Fin n) :
    (marginal (segmentLaw P Q) j : Measure ℝ) = (affineUniform (P j) (Q j) : Measure ℝ) := by
  change Measure.map (fun x : Allocation n => x j)
    (Measure.map (segmentPoint P Q) (unitUniform : Measure ℝ)) = _
  rw [Measure.map_map (measurable_pi_apply j) (measurable_segmentPoint P Q)]
  rfl

theorem segmentLaw_marginal_sorted {n : ℕ} (P Q : Allocation n) (j : Fin n) :
    (marginal (segmentLaw P Q) j : Measure ℝ) = sortedIntervalLaw (P j) (Q j) := by
  rw [segmentLaw_marginal, affineUniform_sorted]

theorem measurable_fullBudget {n : ℕ} (B : ℝ) :
    MeasurableSet {x : Allocation n | FullBudget B x} := by
  have hn : MeasurableSet {x : Allocation n | ∀ j, 0 ≤ x j} := by
    have he : {x : Allocation n | ∀ j, 0 ≤ x j} = ⋂ j : Fin n, {x | 0 ≤ x j} := by
      ext x
      simp
    rw [he]
    exact MeasurableSet.iInter fun j : Fin n =>
      measurableSet_le (measurable_const : Measurable (fun _ : Allocation n => (0 : ℝ)))
        (measurable_pi_apply j)
  have hs : Measurable (fun x : Allocation n => ∑ j, x j) :=
    Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  exact hn.inter (measurableSet_eq_fun hs measurable_const)

theorem segmentLaw_fullBudget {n : ℕ} {B : ℝ} {P Q : Allocation n}
    (hP : FullBudget B P) (hQ : FullBudget B Q) :
    ∀ᵐ x ∂(segmentLaw P Q : Measure (Allocation n)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map (segmentPoint P Q) (unitUniform : Measure ℝ), FullBudget B x
  rw [ae_map_iff (measurable_segmentPoint P Q).aemeasurable (measurable_fullBudget B)]
  exact unitUniform_supported.mono fun t ht => segment_fullBudget hP hQ ht

theorem segmentLaw_supported {n : ℕ} {B : ℝ} {P Q : Allocation n}
    (hP : FullBudget B P) (hQ : FullBudget B Q) : Supported B (segmentLaw P Q) :=
  (segmentLaw_fullBudget hP hQ).mono fun _ hx => fullBudget_feasible hx

namespace ThreeGeometry

theorem vertex_segment_supported (g : ThreeGeometry) (k l : Fin 6) :
    Supported g.budget (segmentLaw (g.vertex k) (g.vertex l)) :=
  segmentLaw_supported (g.vertex_fullBudget k) (g.vertex_fullBudget l)

end ThreeGeometry
end Blotto
