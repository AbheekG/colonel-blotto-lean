import Blotto.RealSegmentFamily
import Blotto.RealUniformHead
import Blotto.ThreeLottery
import Blotto.NestedFirst
import Blotto.RealThreeGeometryCompiler
import Blotto.RealFirstGeometryCompiler

/-! Continuous execution of the first nested conditional table. Positive
geometry and the zero-probability corner share one nine-uniform interface. -/

namespace Blotto.NestedInput
open MeasureTheory Set
open scoped Classical

noncomputable def realFirstPositive (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) (seed : Fin 9 → ℝ) : Allocation 3 :=
  shiftThird s ((RealThreeGeometryCode.compiledLottery (RealNestedParametersCode.firstGeometry i htv s hs hp)).realSampleFlat 0 seed)

theorem realFirstPositive_refines (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) (seed : Fin 9 → ℝ) :
    i.realFirstPositive htv s hs hp seed =
      shiftThird s ((i.firstGeometry htv s hs hp).segmentLottery.realSampleFlat 0 seed) := by
  unfold realFirstPositive
  rw [RealNestedParametersCode.firstGeometry_eq, RealThreeGeometryCode.compiledLottery_eq]

theorem realFirstPositive_law (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) :
    Measure.map (i.realFirstPositive htv s hs hp) (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) =
      (i.firstPositiveLaw htv s hs hp : Measure (Allocation 3)) := by
  have hEq : i.realFirstPositive htv s hs hp =
      shiftThird s ∘ (i.firstGeometry htv s hs hp).segmentLottery.realSampleFlat 0 :=
    funext (i.realFirstPositive_refines htv s hs hp)
  rw [hEq]
  change Measure.map (shiftThird s ∘ (i.firstGeometry htv s hs hp).segmentLottery.realSampleFlat 0) _ = _
  rw [← Measure.map_map (measurable_shiftThird s) ((i.firstGeometry htv s hs hp).segmentLottery.realSampleFlat_measurable 0),
    SegmentLottery.realSampleFlat_law, ThreeGeometry.segmentLottery_law]
  rfl

theorem realFirstPositive_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) (seed : Fin 9 → ℝ)
    (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) : FullBudget i.M (i.realFirstPositive htv s hs hp seed) := by
  rw [i.realFirstPositive_refines]
  let g := i.firstGeometry htv s hs hp
  have hB : g.budget + s = i.M := by
    have h := (i.firstGeometry_matches htv s hs hp).2.2.2.1
    dsimp [g]
    linarith
  have hDraw := g.segmentLottery.realSampleFlat_fullBudget 0 g.segmentLottery_endpoints.1 g.segmentLottery_endpoints.2 seed ht
  change FullBudget i.M (shiftThird s (g.segmentLottery.realSampleFlat 0 seed))
  simpa only [hB] using shiftThird_fullBudget hs.1 hDraw

theorem realFirstPositive_measurable_family (i : NestedInput) (htv : i.t ≤ i.v) :
    Measurable (fun z : i.positiveParameters × (Fin 9 → ℝ) =>
      i.realFirstPositive htv z.1 z.1.property.1 z.1.property.2 z.2) := by
  have hEq : (fun z : i.positiveParameters × (Fin 9 → ℝ) =>
      i.realFirstPositive htv z.1 z.1.property.1 z.1.property.2 z.2) =
      (fun z : i.positiveParameters × (Fin 9 → ℝ) => shiftThird z.1
        ((i.firstGeometry htv z.1 z.1.property.1 z.1.property.2).segmentLottery.realSampleFlat 0 z.2)) := by
    funext z
    exact i.realFirstPositive_refines htv z.1 z.1.property.1 z.1.property.2 z.2
  rw [hEq]
  let g : i.positiveParameters → ThreeGeometry :=
    fun s => i.firstGeometry htv s s.property.1 s.property.2
  have hu : Measurable (fun s => (g s).u) := by dsimp [g, firstGeometry]; fun_prop
  have hv : Measurable (fun s => (g s).v) := by dsimp [g, firstGeometry]; fun_prop
  have hw : Measurable (fun s => (g s).w) := by dsimp [g, firstGeometry]; fun_prop
  have hh : Measurable (fun s => (g s).h) := by dsimp [g, firstGeometry]; fun_prop
  have hDraw := SegmentLottery.realSampleFlat_measurable_joint (fun s => (g s).segmentLottery) 0
    (fun j => ThreeGeometry.measurable_chosenWeights_family g hu hv hw hh j)
    (fun j => ThreeGeometry.measurable_vertex_family g hu hv hw hh (threeEdges j).1)
    (fun j => ThreeGeometry.measurable_vertex_family g hu hv hw hh (threeEdges j).2)
  exact measurable_shiftThird_joint.comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk hDraw)

noncomputable def realFirstZero (i : NestedInput) (s : ℝ) (seed : Fin 9 → ℝ) : Allocation 3 :=
  (RealSegmentPointProgram.output ![0, i.d, s] ![i.a, 0, s] (seed 0)).read

theorem realFirstZero_refines (i : NestedInput) (s : ℝ) (seed : Fin 9 → ℝ) :
    i.realFirstZero s seed = segmentPoint ![0, i.d, s] ![i.a, 0, s] (seed 0) :=
  RealSegmentPointProgram.output_refines _ _ _

theorem realFirstZero_measurable (i : NestedInput) :
    Measurable (fun z : ℝ × (Fin 9 → ℝ) => i.realFirstZero z.1 z.2) := by
  rw [show (fun z : ℝ × (Fin 9 → ℝ) => i.realFirstZero z.1 z.2) =
    fun z => segmentPoint ![0, i.d, z.1] ![i.a, 0, z.1] (z.2 0)
    from funext (fun z => i.realFirstZero_refines z.1 z.2)]
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp [segmentPoint] <;> fun_prop

theorem realFirstZero_law (i : NestedInput) (s : ℝ) :
    Measure.map (i.realFirstZero s) (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) =
      (i.firstZeroLaw s : Measure (Allocation 3)) := by
  rw [show i.realFirstZero s = fun seed => segmentPoint ![0, i.d, s] ![i.a, 0, s] (seed 0)
    from funext (i.realFirstZero_refines s)]
  change Measure.map (segmentPoint ![0, i.d, s] ![i.a, 0, s] ∘ (fun seed : Fin 9 → ℝ => seed 0)) _ = _
  rw [← Measure.map_map (measurable_segmentPoint _ _) (measurable_pi_apply 0), RealUniformInputs.head_law 8]
  rfl

noncomputable def realFirstConditional (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) (seed : Fin 9 → ℝ) : Allocation 3 :=
  if hs : (0 ≤ s ∧ s ≤ i.t) ∧
      0 < RationalNestedParametersCode.conditional.realValue (RealNestedParametersCode.environment i s) then
    i.realFirstPositive htv s hs.1 (by simpa only [RealNestedParametersCode.conditional_value] using hs.2) seed
  else i.realFirstZero s seed

theorem realFirstConditional_refines (i : NestedInput) (htv : i.t ≤ i.v) :
    i.realFirstConditional htv = fun seedLocation seed =>
      if hs : seedLocation ∈ i.positiveParameters then
        i.realFirstPositive htv seedLocation hs.1 hs.2 seed
      else i.realFirstZero seedLocation seed := by
  funext s seed
  simp only [realFirstConditional, RealNestedParametersCode.conditional_value]
  by_cases hs : s ∈ i.positiveParameters
  · have hp : (0 ≤ s ∧ s ≤ i.t) ∧ 0 < i.conditionalProbability s := hs
    simp only [dite_eq_left hs, dite_eq_left hp]
  · have hp : ¬ ((0 ≤ s ∧ s ≤ i.t) ∧ 0 < i.conditionalProbability s) := hs
    simp only [dite_eq_right hs, dite_eq_right hp]

theorem realFirstConditional_law (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) :
    Measure.map (i.realFirstConditional htv s) (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) =
      (i.firstConditionalLaw htv s : Measure (Allocation 3)) := by
  rw [i.realFirstConditional_refines htv]
  change Measure.map (fun seed => if hs : s ∈ i.positiveParameters then
    i.realFirstPositive htv s hs.1 hs.2 seed else i.realFirstZero s seed) _ = _
  by_cases hs : s ∈ i.positiveParameters
  · simpa only [firstConditionalLaw, dite_eq_left hs] using i.realFirstPositive_law htv s hs.1 hs.2
  · simpa only [firstConditionalLaw, dite_eq_right hs] using i.realFirstZero_law s

theorem realFirstConditional_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (seed : Fin 9 → ℝ) (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) :
    FullBudget i.M (i.realFirstConditional htv s seed) := by
  rw [i.realFirstConditional_refines htv]
  change FullBudget i.M (if hp : s ∈ i.positiveParameters then
    i.realFirstPositive htv s hp.1 hp.2 seed else i.realFirstZero s seed)
  split_ifs with hp
  · exact i.realFirstPositive_fullBudget htv s hp.1 hp.2 seed ht
  · have h := i.firstPoint_fullBudget htv hs ht 0
    rw [i.realFirstZero_refines]
    change FullBudget i.M (segmentPoint ![0, i.d, s] ![i.a, 0, s] (seed 0))
    simpa only [firstPoint, dite_eq_right hp] using h

theorem realFirstConditional_measurable (i : NestedInput) (htv : i.t ≤ i.v) :
    Measurable (Function.uncurry (i.realFirstConditional htv)) := by
  rw [i.realFirstConditional_refines htv]
  let S : Set (ℝ × (Fin 9 → ℝ)) := {z | z.1 ∈ i.positiveParameters}
  have hS : MeasurableSet S := i.measurableSet_positiveParameters.preimage measurable_fst
  have hPositive : Measurable (fun z : S =>
      i.realFirstPositive htv z.val.1 z.property.1 z.property.2 z.val.2) := by
    have hParam : Measurable (fun z : S => (⟨z.val.1, z.property⟩ : i.positiveParameters)) :=
      (measurable_fst.comp measurable_subtype_coe).subtype_mk
    have hPair : Measurable (fun z : S =>
        ((⟨z.val.1, z.property⟩ : i.positiveParameters), z.val.2)) :=
      hParam.prodMk (measurable_snd.comp measurable_subtype_coe)
    have hCompose := (i.realFirstPositive_measurable_family htv).comp hPair
    exact hCompose
  have hNegative : Measurable (fun z : (Sᶜ : Set (ℝ × (Fin 9 → ℝ))) => i.realFirstZero z.val.1 z.val.2) :=
    i.realFirstZero_measurable.comp measurable_subtype_coe
  exact hPositive.dite hNegative hS

end Blotto.NestedInput
