import Blotto.RealSecondSampler
import Blotto.RealThirdSampler
import Blotto.NestedCoupling

/-! All three interior nested cases have one eleven-uniform exact-real
interface. The first case leaves one input unused. -/

namespace Blotto.NestedInput
open MeasureTheory
open scoped Classical

noncomputable def realSample (i : NestedInput) (seed : Fin 11 → ℝ) : Allocation 3 :=
  if htv : i.t ≤ i.v then i.realFirstSample htv (Fin.tail seed) else
    if htu : i.u ≤ i.t then i.realSecondSample htu seed else
      i.realThirdSample (lt_of_not_ge htv) (lt_of_not_ge htu) seed

theorem realSample_measurable (i : NestedInput) : Measurable i.realSample := by
  change Measurable (fun seed => if htv : i.t ≤ i.v then _ else if htu : i.u ≤ i.t then _ else _)
  by_cases htv : i.t ≤ i.v
  · simp only [dite_eq_left htv]
    exact (i.realFirstSample_measurable htv).comp (RealUniformInputs.measurable_tail 10)
  · simp only [dite_eq_right htv]
    by_cases htu : i.u ≤ i.t
    · simp only [dite_eq_left htu]
      exact i.realSecondSample_measurable htu
    · simp only [dite_eq_right htu]
      exact i.realThirdSample_measurable (lt_of_not_ge htv) (lt_of_not_ge htu)

theorem realSample_law (i : NestedInput) :
    Measure.map i.realSample (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
      (i.couplingLaw : Measure (Allocation 3)) := by
  change Measure.map (fun seed => if htv : i.t ≤ i.v then _ else if htu : i.u ≤ i.t then _ else _) _ = _
  by_cases htv : i.t ≤ i.v
  · simp only [couplingLaw, dite_eq_left htv]
    change Measure.map (i.realFirstSample htv ∘ (Fin.tail : (Fin 11 → ℝ) → (Fin 10 → ℝ))) _ = _
    rw [← Measure.map_map (i.realFirstSample_measurable htv) (RealUniformInputs.measurable_tail 10),
      RealUniformInputs.tail_law 10]
    exact i.realFirstSample_law htv
  · simp only [couplingLaw, dite_eq_right htv]
    by_cases htu : i.u ≤ i.t
    · simp only [dite_eq_left htu]
      exact i.realSecondSample_law htu
    · simp only [dite_eq_right htu]
      exact i.realThirdSample_law (lt_of_not_ge htv) (lt_of_not_ge htu)

theorem realSample_fullBudget (i : NestedInput) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : FullBudget i.M (i.realSample seed) := by
  unfold realSample
  split_ifs with htv htu
  · exact i.realFirstSample_fullBudget htv (Fin.tail seed) (h 1) (h 2)
  · exact i.realSecondSample_fullBudget htu seed h
  · exact i.realThirdSample_fullBudget (lt_of_not_ge htv) (lt_of_not_ge htu) seed h

theorem realSample_marginals (i : NestedInput) :
    Measure.map (fun seed => i.realSample seed 0) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) = uniformLaw i.a ∧
      Measure.map (fun seed => i.realSample seed 1) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) = uniformLaw i.d ∧
      Measure.map (fun seed => i.realSample seed 2) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) = i.nestedTargetLaw := by
  have hCoordinate (j : Fin 3) :
      Measure.map (fun seed => i.realSample seed j) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
        (marginal i.couplingLaw j : Measure ℝ) := by
    change Measure.map ((fun x : Allocation 3 => x j) ∘ i.realSample) _ = _
    rw [← Measure.map_map (measurable_pi_apply j) i.realSample_measurable, i.realSample_law]
    rfl
  rw [hCoordinate 0, hCoordinate 1, hCoordinate 2]
  exact i.coupling_contract.2

end Blotto.NestedInput
