import Blotto.Boxes

/-! General coordinate permutations of allocation laws and output paths. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

noncomputable def permuteAllocation {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Allocation n) : Allocation n :=
  fun j => x (π j)

theorem measurable_permuteAllocation {n : ℕ} (π : Equiv.Perm (Fin n)) : Measurable (permuteAllocation π) := by
  apply Measurable.of_eval
  intro j
  exact measurable_pi_apply _

theorem permuteAllocation_fullBudget {n : ℕ} (π : Equiv.Perm (Fin n)) {B : ℝ} {x : Allocation n}
    (hx : FullBudget B x) : FullBudget B (permuteAllocation π x) := by
  constructor
  · intro j
    exact hx.1 _
  · change ∑ j, x (π j) = B
    rw [Equiv.sum_comp π]
    exact hx.2

theorem permuteAllocation_inBox {n : ℕ} (π : Equiv.Perm (Fin n)) {length x : Allocation n}
    (hx : InBox length x) : InBox (permuteAllocation π length) (permuteAllocation π x) := fun j => hx (π j)

noncomputable def permuteLaw {n : ℕ} (π : Equiv.Perm (Fin n)) (μ : Mixed n) : Mixed n :=
  μ.map (permuteAllocation π)

theorem permuteLaw_marginal {n : ℕ} (π : Equiv.Perm (Fin n)) (μ : Mixed n) (j : Fin n) :
    (marginal (permuteLaw π μ) j : Measure ℝ) = (marginal μ (π j) : Measure ℝ) := by
  change Measure.map (fun x : Allocation n => x j)
    (Measure.map (permuteAllocation π) (μ : Measure (Allocation n))) = _
  rw [Measure.map_map (measurable_pi_apply j) (measurable_permuteAllocation π)]
  rfl

theorem permuteLaw_fullBudget {n : ℕ} (π : Equiv.Perm (Fin n)) {B : ℝ} {μ : Mixed n}
    (hμ : ∀ᵐ x ∂(μ : Measure (Allocation n)), FullBudget B x) :
    ∀ᵐ x ∂(permuteLaw π μ : Measure (Allocation n)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map (permuteAllocation π) (μ : Measure (Allocation n)), FullBudget B x
  rw [ae_map_iff (measurable_permuteAllocation π).aemeasurable (measurable_fullBudget B)]
  exact hμ.mono fun _ hx => permuteAllocation_fullBudget π hx

end Blotto
