import Blotto.RealFirstConditional
import Blotto.RealConditionalSampling

/-! Exact continuous first nested draw: one location uniform followed by
the jointly measurable conditional table, all from a flat ten-input seed. -/

namespace Blotto.NestedInput
open MeasureTheory

noncomputable def realFirstSample (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ) : Allocation 3 :=
  i.realFirstConditional htv
    (RationalNestedParametersCode.location.realValue (RealNestedParametersCode.environment i (seed 0))) (Fin.tail seed)

theorem realFirstSample_refines (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ) :
    i.realFirstSample htv seed = i.realFirstConditional htv (i.location (seed 0)) (Fin.tail seed) := by
  unfold realFirstSample
  rw [RealNestedParametersCode.location_value]

theorem realFirstSample_input_congr (i j : NestedInput) (hi : i.t ≤ i.v) (hj : j.t ≤ j.v)
    (hij : i = j) (seed : Fin 10 → ℝ) : i.realFirstSample hi seed = j.realFirstSample hj seed := by
  cases hij
  rfl

theorem realFirstSample_measurable (i : NestedInput) (htv : i.t ≤ i.v) :
    Measurable (i.realFirstSample htv) := by
  rw [show i.realFirstSample htv = fun seed => i.realFirstConditional htv (i.location (seed 0)) (Fin.tail seed)
    from funext (i.realFirstSample_refines htv)]
  have hTail : Measurable (fun seed : Fin 10 → ℝ => Fin.tail seed) := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.succ
  exact (i.realFirstConditional_measurable htv).comp
    ((i.measurable_location.comp (measurable_pi_apply 0)).prodMk hTail)

theorem realFirstSample_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ)
    (hr : 0 ≤ seed 0 ∧ seed 0 ≤ 1) (ht : 0 ≤ seed 1 ∧ seed 1 ≤ 1) :
    FullBudget i.M (i.realFirstSample htv seed) := by
  rw [i.realFirstSample_refines]
  exact i.realFirstConditional_fullBudget htv _ (i.location_bounds hr) (Fin.tail seed) ht

theorem realFirstSample_law (i : NestedInput) (htv : i.t ≤ i.v) :
    Measure.map (i.realFirstSample htv) (RealUniformInputs.law 10 : Measure (Fin 10 → ℝ)) =
      (i.firstLaw htv : Measure (Allocation 3)) := by
  rw [RealUniformInputs.map_law_succ 9 _ (i.realFirstSample_measurable htv)]
  have hComp : i.realFirstSample htv ∘ RealUniformInputs.join =
      Function.uncurry (i.realFirstConditional htv) ∘ Prod.map i.location id := by
    funext z
    simp [realFirstSample, RealUniformInputs.join]
    rfl
  rw [hComp, ← Measure.map_map (i.realFirstConditional_measurable htv) (i.measurable_location.prodMap measurable_id)]
  have hProduct := Measure.map_prod_map (unitUniform : Measure ℝ)
    (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) i.measurable_location measurable_id
  rw [Measure.map_id] at hProduct
  rw [← hProduct]
  exact map_product_realizes_family (i.locationLaw : Measure ℝ) (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ))
    (i.realFirstConditional htv) (i.realFirstConditional_measurable htv)
    (fun s => (i.firstConditionalLaw htv s : Measure (Allocation 3))) (i.realFirstConditional_law htv)

theorem realFirstSample_marginals (i : NestedInput) (htv : i.t ≤ i.v) :
    Measure.map (fun seed => i.realFirstSample htv seed 0) (RealUniformInputs.law 10 : Measure (Fin 10 → ℝ)) = uniformLaw i.a ∧
      Measure.map (fun seed => i.realFirstSample htv seed 1) (RealUniformInputs.law 10 : Measure (Fin 10 → ℝ)) = uniformLaw i.d ∧
      Measure.map (fun seed => i.realFirstSample htv seed 2) (RealUniformInputs.law 10 : Measure (Fin 10 → ℝ)) = i.nestedTargetLaw := by
  have hCoordinate (j : Fin 3) :
      Measure.map (fun seed => i.realFirstSample htv seed j) (RealUniformInputs.law 10 : Measure (Fin 10 → ℝ)) =
        (marginal (i.firstLaw htv) j : Measure ℝ) := by
    change Measure.map ((fun x : Allocation 3 => x j) ∘ i.realFirstSample htv) _ = _
    rw [← Measure.map_map (measurable_pi_apply j) (i.realFirstSample_measurable htv), i.realFirstSample_law htv]
    rfl
  rw [hCoordinate 0, hCoordinate 1, hCoordinate 2]
  exact i.firstLaw_marginals htv

end Blotto.NestedInput
