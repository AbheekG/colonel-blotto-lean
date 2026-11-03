import Blotto.ParameterLaw
import Blotto.ThreeMixture
import Blotto.Translate

/-! Measurability of the explicit three-variable construction as its numerical
parameters vary. Proof fields never substitute for a measurable sampler. -/

namespace Blotto.ThreeGeometry
open MeasureTheory Set
open scoped BigOperators

theorem measurable_vertex_family {α : Type*} [MeasurableSpace α]
    (g : α → ThreeGeometry)
    (hu : Measurable fun s => (g s).u) (hv : Measurable fun s => (g s).v)
    (hw : Measurable fun s => (g s).w) (hh : Measurable fun s => (g s).h) (k : Fin 6) :
    Measurable (fun s => (g s).vertex k) := by
  apply Measurable.of_eval
  intro j
  fin_cases k <;> fin_cases j <;>
    simp [vertex, a, d, c] <;> fun_prop

theorem measurable_firstWeights_family {α : Type*} [MeasurableSpace α]
    (g : α → ThreeGeometry)
    (hu : Measurable fun s => (g s).u) (hv : Measurable fun s => (g s).v)
    (hw : Measurable fun s => (g s).w) (hh : Measurable fun s => (g s).h) (i : Fin 9) :
    Measurable (fun s => (g s).firstWeights.vector i) := by
  fin_cases i <;> simp [SegmentWeights.vector, firstWeights, a, c, E, F, G, R] <;> fun_prop

theorem measurable_secondWeights_family {α : Type*} [MeasurableSpace α]
    (g : α → ThreeGeometry)
    (hu : Measurable fun s => (g s).u) (hv : Measurable fun s => (g s).v)
    (hw : Measurable fun s => (g s).w) (hh : Measurable fun s => (g s).h) (i : Fin 9) :
    Measurable (fun s => (g s).secondWeights.vector i) := by
  fin_cases i <;> simp [SegmentWeights.vector, secondWeights, a, c, E, F, G, S] <;> fun_prop

theorem measurable_thirdWeights_family {α : Type*} [MeasurableSpace α]
    (g : α → ThreeGeometry)
    (hu : Measurable fun s => (g s).u) (hv : Measurable fun s => (g s).v)
    (hw : Measurable fun s => (g s).w) (hh : Measurable fun s => (g s).h) (i : Fin 9) :
    Measurable (fun s => (g s).thirdWeights.vector i) := by
  fin_cases i <;> simp [SegmentWeights.vector, thirdWeights, c, E, F, G] <;> fun_prop

theorem measurable_chosenWeights_family {α : Type*} [MeasurableSpace α]
    (g : α → ThreeGeometry)
    (hu : Measurable fun s => (g s).u) (hv : Measurable fun s => (g s).v)
    (hw : Measurable fun s => (g s).w) (hh : Measurable fun s => (g s).h) (i : Fin 9) :
    Measurable (fun s => (g s).chosenWeights.vector i) := by
  have hf := measurable_firstWeights_family g hu hv hw hh i
  have hs := measurable_secondWeights_family g hu hv hw hh i
  have ht := measurable_thirdWeights_family g hu hv hw hh i
  have he : (fun s => (g s).chosenWeights.vector i) =
      (fun s => if (g s).w ≤ (g s).v then (g s).firstWeights.vector i
        else if (g s).w ≤ (g s).u then (g s).secondWeights.vector i else (g s).thirdWeights.vector i) := by
    funext s
    unfold chosenWeights
    split_ifs <;> rfl
  rw [he]
  exact Measurable.ite (measurableSet_le hw hv) hf
    (Measurable.ite (measurableSet_le hw hu) hs ht)

theorem measurable_couplingLaw_family {α : Type*} [MeasurableSpace α]
    (g : α → ThreeGeometry)
    (hu : Measurable fun s => (g s).u) (hv : Measurable fun s => (g s).v)
    (hw : Measurable fun s => (g s).w) (hh : Measurable fun s => (g s).h) :
    Measurable (fun s => ((g s).couplingLaw : Measure (Allocation 3))) := by
  have he : (fun s => ((g s).couplingLaw : Measure (Allocation 3))) =
      (fun s => ∑ i : Fin 9, ENNReal.ofReal ((g s).chosenWeights.vector i) •
        ((g s).edgeLaw i : Measure (Allocation 3))) := by
    funext s
    exact Measure.sum_fintype _
  rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_weighted_law (measurable_chosenWeights_family g hu hv hw hh i)
  exact measurable_segmentLaw_family
    (measurable_vertex_family g hu hv hw hh _) (measurable_vertex_family g hu hv hw hh _)

/-- Adding the parameter to the third coordinate preserves measurability of
this actual finite segment lottery. -/
theorem measurable_shifted_couplingLaw_family {α : Type*} [MeasurableSpace α]
    (g : α → ThreeGeometry) {shift : α → ℝ} (hshift : Measurable shift)
    (hu : Measurable fun s => (g s).u) (hv : Measurable fun s => (g s).v)
    (hw : Measurable fun s => (g s).w) (hh : Measurable fun s => (g s).h) :
    Measurable (fun s => (shiftedLaw (shift s) (g s).couplingLaw : Measure (Allocation 3))) := by
  have he : (fun s => (shiftedLaw (shift s) (g s).couplingLaw : Measure (Allocation 3))) =
      (fun s => ∑ i : Fin 9, ENNReal.ofReal ((g s).chosenWeights.vector i) •
        (segmentLaw (shiftThird (shift s) ((g s).vertex (threeEdges i).1))
          (shiftThird (shift s) ((g s).vertex (threeEdges i).2)) : Measure (Allocation 3))) := by
    funext s
    change Measure.map (shiftThird (shift s))
      (mixtureMeasure (g s).chosenWeights.vector (g s).edgeLaw) = _
    rw [mixtureMeasure_map _ _ _ (measurable_shiftThird (shift s)), Measure.sum_fintype]
    apply Finset.sum_congr rfl
    intro i _
    rw [edgeLaw, shift_segmentLaw]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_weighted_law (measurable_chosenWeights_family g hu hv hw hh i)
  apply measurable_segmentLaw_family
  · exact measurable_shiftThird_joint.comp
      (hshift.prodMk (measurable_vertex_family g hu hv hw hh _))
  · exact measurable_shiftThird_joint.comp
      (hshift.prodMk (measurable_vertex_family g hu hv hw hh _))

end Blotto.ThreeGeometry
