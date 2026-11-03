import Blotto.RealNestedSampler
import Blotto.RealThreeSampler
import Blotto.NestedSpec

/-! The unordered positive-length nested specification also has exact
execution at q=0 and q=1. Its law and scope match the existing NestedSpec. -/

namespace Blotto
open MeasureTheory
open scoped Classical

namespace ThreeSpec

noncomputable def realSample11 (i : ThreeSpec) (seed : Fin 11 → ℝ) : Allocation 3 :=
  i.realSample (RealUniformInputs.dropInputs 9 2 seed)

theorem realSample11_measurable (i : ThreeSpec) : Measurable i.realSample11 :=
  i.realSample_measurable.comp (RealUniformInputs.dropInputs_measurable 9 2)

theorem realSample11_law (i : ThreeSpec) :
    Measure.map i.realSample11 (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
      (i.law : Measure (Allocation 3)) := by
  change Measure.map (i.realSample ∘ RealUniformInputs.dropInputs 9 2) _ = _
  rw [← Measure.map_map i.realSample_measurable (RealUniformInputs.dropInputs_measurable 9 2),
    RealUniformInputs.dropInputs_law 9 2, i.realSample_law]

theorem realSample11_fullBudget (i : ThreeSpec) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : FullBudget i.B (i.realSample11 seed) :=
  i.realSample_fullBudget _ (RealUniformInputs.dropInputs_bounds 9 2 seed h 0)

end ThreeSpec
namespace NestedSpec

noncomputable def realSample (i : NestedSpec) (seed : Fin 11 → ℝ) : Allocation 3 :=
  if hq0 : i.q = 0 then (i.longInput hq0).realSample11 seed else
    if hq1 : i.q = 1 then (i.shortInput hq1).realSample11 seed else
      let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
      if i.a ≤ i.d then j.realSample seed else swapFirst (j.realSample seed)

theorem realSample_measurable (i : NestedSpec) : Measurable i.realSample := by
  change Measurable (fun seed => if hq0 : i.q = 0 then _ else if hq1 : i.q = 1 then _ else _)
  by_cases hq0 : i.q = 0
  · simp only [dite_eq_left hq0]
    exact (i.longInput hq0).realSample11_measurable
  · simp only [dite_eq_right hq0]
    by_cases hq1 : i.q = 1
    · simp only [dite_eq_left hq1]
      exact (i.shortInput hq1).realSample11_measurable
    · simp only [dite_eq_right hq1]
      by_cases had : i.a ≤ i.d
      · simp only [ite_eq_left had]
        exact (i.interiorInput _ _).realSample_measurable
      · simp only [ite_eq_right had]
        exact measurable_swapFirst.comp (i.interiorInput _ _).realSample_measurable

theorem realSample_law (i : NestedSpec) :
    Measure.map i.realSample (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
      (i.law : Measure (Allocation 3)) := by
  change Measure.map (fun seed => if hq0 : i.q = 0 then _ else if hq1 : i.q = 1 then _ else _) _ = _
  by_cases hq0 : i.q = 0
  · simp only [law, dite_eq_left hq0]
    exact (i.longInput hq0).realSample11_law
  · simp only [law, dite_eq_right hq0]
    by_cases hq1 : i.q = 1
    · simp only [dite_eq_left hq1]
      exact (i.shortInput hq1).realSample11_law
    · simp only [dite_eq_right hq1]
      by_cases had : i.a ≤ i.d
      · simp only [ite_eq_left had]
        exact (i.interiorInput _ _).realSample_law
      · simp only [ite_eq_right had]
        let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
        change Measure.map (swapFirst ∘ j.realSample) _ = (swapLaw j.couplingLaw : Measure (Allocation 3))
        rw [← Measure.map_map measurable_swapFirst j.realSample_measurable, j.realSample_law]
        rfl

theorem realSample_fullBudget (i : NestedSpec) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : FullBudget i.M (i.realSample seed) := by
  unfold realSample
  split_ifs with hq0 hq1 had
  · exact (i.longInput hq0).realSample11_fullBudget seed h
  · exact (i.shortInput hq1).realSample11_fullBudget seed h
  · exact (i.interiorInput _ _).realSample_fullBudget seed h
  · exact swapFirst_fullBudget ((i.interiorInput _ _).realSample_fullBudget seed h)

theorem realSample_marginals (i : NestedSpec) :
    Measure.map (fun seed => i.realSample seed 0) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) = uniformLaw i.a ∧
      Measure.map (fun seed => i.realSample seed 1) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) = uniformLaw i.d ∧
      Measure.map (fun seed => i.realSample seed 2) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
        affineMeasure i.q (uniformLaw i.t) (uniformLaw i.c) := by
  have hCoordinate (j : Fin 3) :
      Measure.map (fun seed => i.realSample seed j) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
        (marginal i.law j : Measure ℝ) := by
    change Measure.map ((fun x : Allocation 3 => x j) ∘ i.realSample) _ = _
    rw [← Measure.map_map (measurable_pi_apply j) i.realSample_measurable, i.realSample_law]
    rfl
  rw [hCoordinate 0, hCoordinate 1, hCoordinate 2]
  exact i.law_contract.2

end NestedSpec
end Blotto
