import Blotto.ParameterLaw
import Blotto.ThreeCoupling

/-! Exact translations used by conditional constant-sum couplings. -/

namespace Blotto
open MeasureTheory Set

noncomputable def shiftThird (s : ℝ) (x : Allocation 3) : Allocation 3 :=
  ![x 0, x 1, x 2 + s]

theorem measurable_shiftThird (s : ℝ) : Measurable (shiftThird s) := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp [shiftThird] <;> fun_prop

theorem measurable_shiftThird_joint : Measurable (fun z : ℝ × Allocation 3 => shiftThird z.1 z.2) := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp [shiftThird] <;> fun_prop

noncomputable def shiftedLaw (s : ℝ) (μ : Mixed 3) : Mixed 3 := μ.map (shiftThird s)

theorem shiftThird_fullBudget {B s : ℝ} {x : Allocation 3}
    (hs : 0 ≤ s) (hx : FullBudget B x) : FullBudget (B + s) (shiftThird s x) := by
  constructor
  · intro j
    fin_cases j
    · exact hx.1 0
    · exact hx.1 1
    · exact add_nonneg (hx.1 2) hs
  · have hsum := hx.2
    simp [Fin.sum_univ_succ] at hsum
    simp [shiftThird, Fin.sum_univ_succ]
    linarith

theorem shiftedLaw_fullBudget {B s : ℝ} {μ : Mixed 3} (hs : 0 ≤ s)
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget B x) :
    ∀ᵐ x ∂(shiftedLaw s μ : Measure (Allocation 3)), FullBudget (B + s) x := by
  change ∀ᵐ x ∂Measure.map (shiftThird s) (μ : Measure (Allocation 3)), FullBudget (B + s) x
  rw [ae_map_iff (measurable_shiftThird s).aemeasurable (measurable_fullBudget (B + s))]
  exact hμ.mono fun _ hx => shiftThird_fullBudget hs hx

theorem shiftedLaw_marginal_zero (s : ℝ) (μ : Mixed 3) :
    (marginal (shiftedLaw s μ) 0 : Measure ℝ) = marginal μ 0 := by
  change Measure.map (fun x : Allocation 3 => x 0)
    (Measure.map (shiftThird s) (μ : Measure (Allocation 3))) = _
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_shiftThird s)]
  rfl

theorem shiftedLaw_marginal_one (s : ℝ) (μ : Mixed 3) :
    (marginal (shiftedLaw s μ) 1 : Measure ℝ) = marginal μ 1 := by
  change Measure.map (fun x : Allocation 3 => x 1)
    (Measure.map (shiftThird s) (μ : Measure (Allocation 3))) = _
  rw [Measure.map_map (measurable_pi_apply 1) (measurable_shiftThird s)]
  rfl

theorem shiftedLaw_marginal_two (s : ℝ) (μ : Mixed 3) :
    (marginal (shiftedLaw s μ) 2 : Measure ℝ) =
      Measure.map (fun t => t + s) (marginal μ 2 : Measure ℝ) := by
  change Measure.map (fun x : Allocation 3 => x 2)
    (Measure.map (shiftThird s) (μ : Measure (Allocation 3))) =
      Measure.map (fun t => t + s) (Measure.map (fun x : Allocation 3 => x 2) (μ : Measure (Allocation 3)))
  rw [Measure.map_map (measurable_pi_apply 2) (measurable_shiftThird s),
    Measure.map_map (g := fun t : ℝ => t + s) (measurable_id.add measurable_const) (measurable_pi_apply 2)]
  rfl

theorem shift_affineUniform (s a b : ℝ) :
    Measure.map (fun t => t + s) (affineUniform a b : Measure ℝ) =
      (affineUniform (a + s) (b + s) : Measure ℝ) := by
  change Measure.map (fun t => t + s) (Measure.map (affineLine a b) (unitUniform : Measure ℝ)) =
    Measure.map (affineLine (a + s) (b + s)) (unitUniform : Measure ℝ)
  rw [Measure.map_map (g := fun t : ℝ => t + s) (measurable_id.add measurable_const) (measurable_affineLine a b)]
  congr 1
  funext t
  dsimp [Function.comp_def, affineLine]
  ring

theorem shift_zeroUniformLaw (s c p : ℝ) (hsc : s < c) :
    Measure.map (fun t => t + s) (zeroUniformLaw (c - s) p) =
      ENNReal.ofReal (1 - p) • Measure.dirac s +
        ENNReal.ofReal p • (affineUniform s c : Measure ℝ) := by
  have hf : Measurable (fun t : ℝ => t + s) := measurable_id.add measurable_const
  have hU : uniformLaw (c - s) = (affineUniform 0 (c - s) : Measure ℝ) := by
    rw [affineUniform_increasing (sub_pos.mpr hsc)]
    simp only [intervalLaw, sub_zero, uniformLaw]
  rw [zeroUniformLaw, Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf, zero_add,
    hU, shift_affineUniform, zero_add, sub_add_cancel]

/-- Translation commutes with a uniformly sampled segment, including constant
coordinate projections. -/
theorem shift_segmentLaw (s : ℝ) (P Q : Allocation 3) :
    Measure.map (shiftThird s) (segmentLaw P Q : Measure (Allocation 3)) =
      (segmentLaw (shiftThird s P) (shiftThird s Q) : Measure (Allocation 3)) := by
  change Measure.map (shiftThird s) (Measure.map (segmentPoint P Q) (unitUniform : Measure ℝ)) =
    Measure.map (segmentPoint (shiftThird s P) (shiftThird s Q)) (unitUniform : Measure ℝ)
  rw [Measure.map_map (measurable_shiftThird s) (measurable_segmentPoint P Q)]
  congr 1
  funext t j
  fin_cases j
  · rfl
  · rfl
  · dsimp [Function.comp_def, shiftThird, segmentPoint]
    ring

end Blotto
