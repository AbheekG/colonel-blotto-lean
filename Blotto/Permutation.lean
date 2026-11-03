import Blotto.Segments

/-! Coordinate swaps of actual probability laws preserve hard budgets.
The operation permutes one player's allocation, without changing how the
players' independent laws are combined. -/

namespace Blotto
open MeasureTheory Set

noncomputable def swapFirst (x : Allocation 3) : Allocation 3 := ![x 1, x 0, x 2]

noncomputable def swapIndex : Fin 3 → Fin 3 := ![1, 0, 2]

theorem swapFirst_eval (x : Allocation 3) (j : Fin 3) : swapFirst x j = x (swapIndex j) := by
  fin_cases j <;> rfl

theorem measurable_swapFirst : Measurable swapFirst := by
  apply Measurable.of_eval
  intro j
  simp only [swapFirst_eval]
  exact measurable_pi_apply _

theorem swapFirst_fullBudget {B : ℝ} {x : Allocation 3} (hx : FullBudget B x) :
    FullBudget B (swapFirst x) := by
  constructor
  · intro j
    rw [swapFirst_eval]
    exact hx.1 _
  · have hs := hx.2
    simp [Fin.sum_univ_succ] at hs
    simp [swapFirst, Fin.sum_univ_succ]
    linarith

noncomputable def swapLaw (μ : Mixed 3) : Mixed 3 := μ.map swapFirst

theorem swapLaw_marginal (μ : Mixed 3) (j : Fin 3) :
    (marginal (swapLaw μ) j : Measure ℝ) = marginal μ (swapIndex j) := by
  change Measure.map (fun x : Allocation 3 => x j)
    (Measure.map swapFirst (μ : Measure (Allocation 3))) = _
  rw [Measure.map_map (measurable_pi_apply j) measurable_swapFirst]
  simp only [Function.comp_def, swapFirst_eval]
  rfl

theorem swapLaw_fullBudget {B : ℝ} {μ : Mixed 3}
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget B x) :
    ∀ᵐ x ∂(swapLaw μ : Measure (Allocation 3)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map swapFirst (μ : Measure (Allocation 3)), FullBudget B x
  rw [ae_map_iff measurable_swapFirst.aemeasurable (measurable_fullBudget B)]
  exact hμ.mono fun _ hx => swapFirst_fullBudget hx

end Blotto
