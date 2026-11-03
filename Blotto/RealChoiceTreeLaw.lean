import Blotto.RealChoiceTree

/-! Adaptive threshold execution with independent real inputs realizes the
exact declared whole law whenever the supplied choice budget covers the tree. -/

namespace Blotto.RealChoiceTree
open MeasureTheory
open scoped BigOperators

theorem map_constant {S α : Type*} [MeasurableSpace S] [MeasurableSpace α]
    (μ : ProbabilityMeasure S) (x : α) : Measure.map (fun _ : S => x) (μ : Measure S) = Measure.dirac x := by
  rw [Measure.map_const]
  simp

theorem output_law {α : Type*} [MeasurableSpace α] (T : RealChoiceTree α) (C : ℕ)
    (fallback : α) (h : T.height ≤ C) :
    Measure.map (T.output C fallback) (RealUniformInputs.law C : Measure (Fin C → ℝ)) =
      (T.idealLaw : Measure α) := by
  induction C generalizing T with
  | zero =>
    cases T with
    | leaf x =>
      change Measure.map (fun _ : Fin 0 → ℝ => x) (RealUniformInputs.law 0 : Measure (Fin 0 → ℝ)) = Measure.dirac x
      exact map_constant _ x
    | fork p hp upper lower => simp [height] at h
  | succ C ih =>
    cases T with
    | leaf x =>
      change Measure.map (fun _ : Fin (C + 1) → ℝ => x) (RealUniformInputs.law (C + 1) : Measure (Fin (C + 1) → ℝ)) = Measure.dirac x
      exact map_constant _ x
    | fork p hp upper lower =>
      have hUpper : upper.height ≤ C := by simp only [height] at h; omega
      have hLower : lower.height ≤ C := by simp only [height] at h; omega
      rw [RealUniformInputs.map_law_succ C _ ((fork p hp upper lower).measurable_output (C + 1) fallback)]
      have hJoin : (fork p hp upper lower).output (C + 1) fallback ∘ RealUniformInputs.join =
          RealIndependentChoice.sample p (upper.output C fallback) (lower.output C fallback) := by
        funext z
        rw [Function.comp_apply, output_fork_succ]
        rfl
      rw [hJoin, RealIndependentChoice.map_product p hp _ _ _ (upper.measurable_output C fallback) (lower.measurable_output C fallback),
        ih upper hUpper, ih lower hLower]
      simp [idealLaw, probabilityMixture, mixtureMeasure, Measure.sum_fintype, Fin.sum_univ_succ]

end Blotto.RealChoiceTree
