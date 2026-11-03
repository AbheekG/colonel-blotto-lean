import Blotto.RealNestedResourceSource
import Blotto.RealRoundingKernel

/-! The indexed resource source and fresh terminal uniforms realize the
existing whole three-resource coupling. Only reached valid terminals are
used in the measurability/law proof. -/

namespace Blotto.NestedResourceSystem
open MeasureTheory
open scoped Classical

noncomputable def realInputLaw : ProbabilityMeasure ((Fin 2 → ℝ) × (Fin 11 → ℝ)) :=
  RealUniformInputs.productLaw (RealUniformInputs.law 2) (RealUniformInputs.law 11)

noncomputable def realLeafSample (i : NestedResourceSystem) (r : Allocation 3) (seed : Fin 11 → ℝ) : Allocation 3 :=
  if hr : i.Valid r then (i.terminal r hr).realSample seed else 0

theorem realLeafSample_measurable (i : NestedResourceSystem) (r : Allocation 3) (hr : i.Valid r) :
    Measurable (i.realLeafSample r) := by
  change Measurable (fun seed => if h : i.Valid r then _ else _)
  simp only [dite_eq_left hr]
  exact (i.terminal r hr).realSample_measurable

theorem realLeafSample_law (i : NestedResourceSystem) (r : Allocation 3) (hr : i.Valid r) :
    Measure.map (i.realLeafSample r) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
      (i.leafLaw r : Measure (Allocation 3)) := by
  change Measure.map (fun seed => if h : i.Valid r then _ else _) _ = _
  simp only [leafLaw, dite_eq_left hr]
  exact (i.terminal r hr).realSample_law

theorem realSample_refines_kernel (i : NestedResourceSystem) (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) :
    i.realSample seed = i.tree.realKernel 2 i.initial i.realLeafSample seed := by
  change i.realSample seed = i.realLeafSample (i.tree.realChoice.output 2 i.initial seed.1) seed.2
  rw [← i.realPhase_refines, realLeafSample, dite_eq_left (i.realPhase_valid seed.1)]
  rfl

theorem realSample_measurable (i : NestedResourceSystem) : Measurable i.realSample := by
  have hEq : i.realSample = i.tree.realKernel 2 i.initial i.realLeafSample := funext i.realSample_refines_kernel
  rw [hEq]
  exact i.tree.realKernel_measurable 2 i.initial i.realLeafSample
    (i.tree.forLeaves_mono (fun r hr => i.realLeafSample_measurable r hr) i.tree_valid) i.tree_height

theorem realSample_law (i : NestedResourceSystem) :
    Measure.map i.realSample (realInputLaw : Measure ((Fin 2 → ℝ) × (Fin 11 → ℝ))) =
      (i.law : Measure (Allocation 3)) := by
  have hEq : i.realSample = i.tree.realKernel 2 i.initial i.realLeafSample := funext i.realSample_refines_kernel
  rw [hEq]
  exact i.tree.realKernel_law 2 i.initial (RealUniformInputs.law 11) i.realLeafSample i.leafLaw
    (i.tree.forLeaves_mono (fun r hr => i.realLeafSample_measurable r hr) i.tree_valid)
    (i.tree.forLeaves_mono (fun r hr => i.realLeafSample_law r hr) i.tree_valid) i.tree_height

end Blotto.NestedResourceSystem
