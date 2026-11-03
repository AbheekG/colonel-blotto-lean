import Blotto.RationalFourInput
import Blotto.RationalNestedResourceSystem
import Blotto.RationalFourParameterTable
import Blotto.RationalFourFactoryEquality

/-! Native reflected-resource initialization in the atom-conditioning
branch. Its exact real system is the maintained three-resource construction. -/

namespace Blotto.RationalFourInput
open scoped BigOperators

theorem originalLengths_le_w (i : RationalFourInput) (j : Fin 3) : i.originalLengths j ≤ i.w := by
  fin_cases j
  · exact i.uv.trans i.vw
  · exact i.vw
  · exact le_rfl

theorem short_capacity (i : RationalFourInput) (j : Fin 3) :
    i.originalLengths j - i.shortFraction * i.originalLengths j = i.scaleFraction * i.originalLengths j := by
  dsimp [scaleFraction]
  ring

theorem scaled_resource_identity (i : RationalFourInput) :
    i.scaleFraction * i.S = i.S - (1 - i.p) * i.ell ∧
      i.nestedProbability * i.scaleFraction * i.S = i.p * i.ell := by
  have h := i.real.scaled_resource_identity
  rw [← i.scaleFraction_real, ← i.S_real, ← i.nestedProbability_real] at h
  dsimp only [real] at h
  exact_mod_cast h

def reflectedResourceSystemReference (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : RationalNestedResourceSystem where
  M := i.reflectedBudget
  long := i.originalLengths
  short := fun j => i.shortFraction * i.originalLengths j
  initial := fun j => i.nestedProbability * i.scaleFraction * i.originalLengths j
  short_pos := fun j => mul_pos i.shortFraction_bounds.1 (i.originalLengths_pos j)
  short_lt := by
    intro j
    simpa only [one_mul] using mul_lt_mul_of_pos_right i.shortFraction_bounds.2 (i.originalLengths_pos j)
  long_le := fun j => (i.originalLengths_le_w j).trans (le_of_lt (i.reflected_budget_bounds hcase).1)
  initial_box := by
    intro j
    have hC := mul_pos i.scaleFraction_bounds.1 (i.originalLengths_pos j)
    constructor
    · simpa only [mul_assoc] using mul_nonneg (le_of_lt i.nestedProbability_bounds.1) (le_of_lt hC)
    · rw [i.short_capacity]
      simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right (le_of_lt i.nestedProbability_bounds.2) (le_of_lt hC)
  initial_mean := by
    rw [Finset.sum_sub_distrib, i.originalLengths_sum]
    have hr : (∑ j, i.nestedProbability * i.scaleFraction * i.originalLengths j) = i.p * i.ell := by
      rw [← Finset.mul_sum, i.originalLengths_sum]
      exact i.scaled_resource_identity.2
    rw [hr]
    dsimp [reflectedBudget]
    ring

def reflectedResourceSystem (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : RationalNestedResourceSystem :=
  let p := RationalFourParameterTable.prepare i
  { M := p.reflectedBudget
    long := i.originalLengths
    short := fun j => p.shortFraction * i.originalLengths j
    initial := fun j => p.nestedProbability * p.scaleFraction * i.originalLengths j
    short_pos := by intro j; rw [p.shortFraction_eq]; exact (i.reflectedResourceSystemReference hcase).short_pos j
    short_lt := by intro j; rw [p.shortFraction_eq]; exact (i.reflectedResourceSystemReference hcase).short_lt j
    long_le := by intro j; rw [p.reflectedBudget_eq]; exact (i.reflectedResourceSystemReference hcase).long_le j
    initial_box := by
      intro j
      rw [p.nestedProbability_eq, p.scaleFraction_eq, p.shortFraction_eq]
      exact (i.reflectedResourceSystemReference hcase).initial_box j
    initial_mean := by
      rw [p.nestedProbability_eq, p.scaleFraction_eq, p.reflectedBudget_eq]
      exact (i.reflectedResourceSystemReference hcase).initial_mean }

theorem reflectedResourceSystem_refines (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    i.reflectedResourceSystem hcase = i.reflectedResourceSystemReference hcase := by
  apply RationalNestedResourceSystem.eq_of_data
  · exact (RationalFourParameterTable.prepare i).reflectedBudget_eq
  · rfl
  · funext j
    change (RationalFourParameterTable.prepare i).shortFraction * i.originalLengths j = _
    rw [RationalFourParameterTable.shortFraction_eq]
    rfl
  · funext j
    change (RationalFourParameterTable.prepare i).nestedProbability *
      (RationalFourParameterTable.prepare i).scaleFraction * i.originalLengths j = _
    rw [RationalFourParameterTable.nestedProbability_eq, RationalFourParameterTable.scaleFraction_eq]
    rfl

theorem reflectedResourceSystem_real (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (i.reflectedResourceSystem hcase).real = i.real.reflectedResourceSystem (i.smallCase_real hcase) := by
  rw [i.reflectedResourceSystem_refines]
  apply NestedResourceSystem.eq_of_data
  · exact i.reflectedBudget_real
  · exact i.originalLengths_real
  · funext j
    change ((i.shortFraction * i.originalLengths j : ℚ) : ℝ) = i.real.shortFraction * i.real.originalLengths j
    rw [Rat.cast_mul, i.shortFraction_real, congrFun i.originalLengths_real j]
  · funext j
    change ((i.nestedProbability * i.scaleFraction * i.originalLengths j : ℚ) : ℝ) =
      i.real.nestedProbability * i.real.scaleFraction * i.real.originalLengths j
    rw [Rat.cast_mul, Rat.cast_mul, i.nestedProbability_real, i.scaleFraction_real, congrFun i.originalLengths_real j]

end Blotto.RationalFourInput
