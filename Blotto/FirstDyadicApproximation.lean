import Blotto.FirstLocationApproximation
import Blotto.FirstConditionalDyadic
import Blotto.AverageFinitePoints

/-! The first nested case with both scalar uniforms replaced by K-bit
midpoints: an actual finite whole law, error at most 3/(2*2^K), and exact
budgets on every pair of bit vectors and every component slot. Branch
probabilities remain exact; bounded rational-coin access is separate. -/

namespace Blotto.NestedInput
open MeasureTheory
open scoped BigOperators

noncomputable def firstDyadicApproximation (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) : Mixed 3 :=
  probabilityMixture (fun _ : Fin (2 ^ K) => 1 / ((2 ^ K : ℕ) : ℝ))
    (fun j => i.firstConditionalDyadicLaw htv (i.location (midpoint j)) K)
    (fun _ => by positivity) (uniformWeights_sum (pow_pos (by decide : 0 < (2 : ℕ)) K))

theorem firstLocationApproximation_eq_mixture (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    i.firstLocationApproximation htv K =
      probabilityMixture (fun _ : Fin (2 ^ K) => 1 / ((2 ^ K : ℕ) : ℝ))
        (fun j => i.firstConditionalLaw htv (i.location (midpoint j)))
        (fun _ => by positivity) (uniformWeights_sum (pow_pos (by decide : 0 < (2 : ℕ)) K)) := by
  unfold firstLocationApproximation firstParametricLaw dyadicLocationLaw
  rw [dyadicMidpointLaw_eq]
  exact averaged_finiteUniform_map _ _ _ i.measurable_location _ (i.measurable_firstConditionalLaw htv)

theorem firstDyadicApproximation_inner_error (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    CDFClose (i.firstDyadicApproximation htv K) (i.firstLocationApproximation htv K) (1 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.firstLocationApproximation_eq_mixture htv K]
  exact probabilityMixture_CDFClose _ _ _ _ _ (fun j => i.firstConditionalDyadicLaw_CDF_error htv _ K)

theorem firstDyadicApproximation_CDF_error (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    CDFClose (i.firstDyadicApproximation htv K) (i.firstLaw htv) (3 / (2 * (2 : ℝ) ^ K)) := by
  have he := (i.firstDyadicApproximation_inner_error htv K).triangle (i.firstLocationApproximation_CDF_error htv K)
  have hr : 1 / (2 * (2 : ℝ) ^ K) + 1 / (2 : ℝ) ^ K = 3 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hr] at he
  exact he

theorem firstDyadicApproximation_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    ∀ᵐ x ∂(i.firstDyadicApproximation htv K : Measure (Allocation 3)), FullBudget i.M x := by
  apply probabilityMixture_ae
  intro j
  exact i.firstConditionalDyadicLaw_fullBudget htv
    (i.location_bounds ⟨le_of_lt (midpoint_bounds (pow_pos (by decide : 0 < (2 : ℕ)) K) j).1,
      le_of_lt (midpoint_bounds (pow_pos (by decide : 0 < (2 : ℕ)) K) j).2⟩) K

noncomputable def firstDyadicPoint (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) : Allocation 3 :=
  i.firstConditionalDyadicPoint htv (i.location (dyadicMidpointSample K outerBits)) K slot innerBits

theorem firstDyadicPoint_fullBudget (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) :
    FullBudget i.M (i.firstDyadicPoint htv K outerBits innerBits slot) :=
  i.firstConditionalDyadicPoint_fullBudget htv (i.dyadicLocation_point_bounds K outerBits) K slot innerBits

end Blotto.NestedInput
