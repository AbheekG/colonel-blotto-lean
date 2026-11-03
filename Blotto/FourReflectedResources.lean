import Blotto.FourSmallParameters
import Blotto.ReflectAppend

/-! Instantiates the three-resource rounding system in the atom-conditioning
branch, and constructs its reflected zero-fourth-coordinate law. -/

namespace Blotto.FourInput
open MeasureTheory Set
open scoped BigOperators

noncomputable def originalLengths (i : FourInput) : Allocation 3 := ![i.u, i.v, i.w]

theorem originalLengths_pos (i : FourInput) (j : Fin 3) : 0 < i.originalLengths j := by
  fin_cases j
  · exact i.u_pos
  · exact i.lengths_positive.1
  · exact i.lengths_positive.2.1

theorem originalLengths_le_w (i : FourInput) (j : Fin 3) : i.originalLengths j ≤ i.w := by
  fin_cases j
  · exact le_trans i.uv i.vw
  · exact i.vw
  · exact le_rfl

theorem originalLengths_sum (i : FourInput) : ∑ j, i.originalLengths j = i.S := by
  simp [originalLengths, S, Fin.sum_univ_succ, add_assoc]

theorem short_capacity (i : FourInput) (j : Fin 3) :
    i.originalLengths j - i.shortFraction * i.originalLengths j = i.scaleFraction * i.originalLengths j := by
  dsimp [scaleFraction]
  ring

noncomputable def reflectedResourceSystem (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) : NestedResourceSystem where
  M := i.reflectedBudget
  long := i.originalLengths
  short := fun j => i.shortFraction * i.originalLengths j
  initial := fun j => i.nestedProbability * i.scaleFraction * i.originalLengths j
  short_pos := fun j => mul_pos i.shortFraction_bounds.1 (i.originalLengths_pos j)
  short_lt := by
    intro j
    have he := mul_lt_mul_of_pos_right i.shortFraction_bounds.2 (i.originalLengths_pos j)
    simpa only [one_mul] using he
  long_le := fun j => le_trans (i.originalLengths_le_w j) (le_of_lt (i.reflected_budget_bounds hcase).1)
  initial_box := by
    intro j
    have hC := mul_pos i.scaleFraction_bounds.1 (i.originalLengths_pos j)
    change 0 ≤ i.nestedProbability * i.scaleFraction * i.originalLengths j ∧
      i.nestedProbability * i.scaleFraction * i.originalLengths j ≤
        i.originalLengths j - i.shortFraction * i.originalLengths j
    constructor
    · simpa only [mul_assoc] using mul_nonneg (le_of_lt i.nestedProbability_bounds.1) (le_of_lt hC)
    · rw [i.short_capacity j]
      have he := mul_le_mul_of_nonneg_right (le_of_lt i.nestedProbability_bounds.2) (le_of_lt hC)
      simpa only [mul_assoc, one_mul] using he
  initial_mean := by
    rw [Finset.sum_sub_distrib, i.originalLengths_sum]
    have hr : (∑ j, i.nestedProbability * i.scaleFraction * i.originalLengths j) = i.p * i.ell := by
      rw [← Finset.mul_sum, i.originalLengths_sum]
      exact i.scaled_resource_identity.2
    rw [hr]
    dsimp [reflectedBudget]
    ring

theorem reflected_initial_weight (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (j : Fin 3) :
    (i.reflectedResourceSystem hcase).initialWeight j = i.nestedProbability := by
  change i.nestedProbability * i.scaleFraction * i.originalLengths j /
    (i.originalLengths j - i.shortFraction * i.originalLengths j) = _
  rw [i.short_capacity j]
  field_simp [ne_of_gt i.scaleFraction_bounds.1, ne_of_gt (i.originalLengths_pos j)]

noncomputable def reflectedZeroLaw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) : Mixed 4 :=
  reflectedLaw i.originalLengths (i.reflectedResourceSystem hcase).law

theorem reflectedZeroLaw_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    ∀ᵐ x ∂(i.reflectedZeroLaw hcase : Measure (Allocation 4)), FullBudget i.B x := by
  have hS : ∑ j, i.originalLengths j = i.B + i.reflectedBudget := by
    rw [i.originalLengths_sum, (i.reflected_budget_bounds hcase).2]
    ring
  exact reflectedLaw_fullBudget _ _ hS (i.reflectedResourceSystem hcase).law_contract.1
    (i.reflectedResourceSystem hcase).law_inBox

theorem reflectedZeroLaw_marginal (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (j : Fin 3) :
    (marginal (i.reflectedZeroLaw hcase) j.castSucc : Measure ℝ) =
      ENNReal.ofReal i.nestedProbability •
        (affineUniform (i.scaleFraction * i.originalLengths j) (i.originalLengths j) : Measure ℝ) +
      ENNReal.ofReal (1 - i.nestedProbability) • uniformLaw (i.originalLengths j) := by
  rw [reflectedZeroLaw, reflectedLaw_marginal_first, (i.reflectedResourceSystem hcase).law_contract.2 j,
    i.reflected_initial_weight hcase j]
  change Measure.map (fun y => i.originalLengths j - y)
    (affineMeasure i.nestedProbability (uniformLaw (i.shortFraction * i.originalLengths j))
      (uniformLaw (i.originalLengths j))) = _
  have hf : Measurable (fun y : ℝ => i.originalLengths j - y) := measurable_const.sub measurable_id
  rw [affineMeasure, Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable,
    reflect_uniformLaw (mul_pos i.shortFraction_bounds.1 (i.originalLengths_pos j)),
    reflect_uniformLaw (i.originalLengths_pos j), i.short_capacity j, sub_self,
    affineUniform_zero_uniformLaw (i.originalLengths_pos j)]

theorem reflectedZeroLaw_last (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (marginal (i.reflectedZeroLaw hcase) 3 : Measure ℝ) = Measure.dirac 0 :=
  reflectedLaw_marginal_last _ _

noncomputable def reflectedZeroPoint (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (choice : ℕ → Bool) (useFamily : Bool) (r t : ℝ) (edge : Fin 9) (residualEdge : Fin 3) : Allocation 4 :=
  reflectAppend i.originalLengths ((i.reflectedResourceSystem hcase).point choice useFamily r t edge residualEdge)

theorem reflectedZeroPoint_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (choice : ℕ → Bool) (useFamily : Bool) {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (edge : Fin 9) (residualEdge : Fin 3) : FullBudget i.B (i.reflectedZeroPoint hcase choice useFamily r t edge residualEdge) := by
  have hS : ∑ j, i.originalLengths j = i.B + i.reflectedBudget := by
    rw [i.originalLengths_sum, (i.reflected_budget_bounds hcase).2]
    ring
  have hp := (i.reflectedResourceSystem hcase).point_contract choice useFamily hr ht edge residualEdge
  exact reflectAppend_fullBudget hS hp.1 hp.2

end Blotto.FourInput
