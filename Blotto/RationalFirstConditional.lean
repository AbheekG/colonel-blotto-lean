import Blotto.RationalNestedInput
import Blotto.RationalLotteryTranslate
import Blotto.FirstConditionalDyadic
import Blotto.RationalSegmentFlat

/-! The dependent first-case conditional table is computed in rationals.
Its exact whole law and every midpoint path agree with the maintained real
conditional construction, including the zero-probability corner. -/

namespace Blotto.RationalNestedInput
open MeasureTheory Set

theorem firstCase_real (i : RationalNestedInput) (htv : i.t ≤ i.v) : i.real.t ≤ i.real.v := by
  rw [← i.v_real]
  change (i.t : ℝ) ≤ (i.v : ℝ)
  exact_mod_cast htv

theorem interval_real (i : RationalNestedInput) {s : ℚ} (hs : 0 ≤ s ∧ s ≤ i.t) :
    (s : ℝ) ∈ Icc 0 i.real.t := by
  change (0 : ℝ) ≤ s ∧ (s : ℝ) ≤ (i.t : ℝ)
  exact_mod_cast hs

def firstConditionalLottery (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) : RationalSegmentLottery 3 9 :=
  if hp : 0 < i.conditionalProbability s then
    ((i.firstGeometry htv s hs hp).segmentLottery).shiftThird s
  else
    ⟨(fun slot => if slot = 0 then 1 else 0), (fun _ => ![0, i.d, s]), (fun _ => ![i.a, 0, s]),
      (by intro slot; split_ifs <;> norm_num), (by simp)⟩

theorem firstConditionalLottery_law (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) :
    (i.firstConditionalLottery htv s hs).real.law = i.real.firstConditionalLaw (i.firstCase_real htv) s := by
  have hsR := i.interval_real hs
  have he : 0 < i.conditionalProbability s ↔ 0 < i.real.conditionalProbability s := by
    rw [← i.conditionalProbability_real]
    norm_cast
  unfold firstConditionalLottery NestedInput.firstConditionalLaw
  by_cases hp : 0 < i.conditionalProbability s
  · rw [dite_eq_left hp, dite_eq_left (show (s : ℝ) ∈ i.real.positiveParameters from ⟨hsR, he.mp hp⟩)]
    rw [RationalSegmentLottery.shiftThird_law, RationalThreeGeometry.segmentLottery_real, i.firstGeometry_real]
    unfold NestedInput.firstPositiveLaw
    congr 1
  · have hn : (s : ℝ) ∉ i.real.positiveParameters := fun h => hp (he.mpr h.2)
    rw [dite_eq_right hp, dite_eq_right hn]
    apply ProbabilityMeasure.toMeasure_injective
    simp [RationalSegmentLottery.real, SegmentLottery.law, probabilityMixture, mixtureMeasure,
      Measure.sum_fintype, Fin.sum_univ_succ, NestedInput.firstZeroLaw, real]
    congr 1
    congr 1
    all_goals funext j; fin_cases j <;> simp

theorem firstConditionalLottery_point (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) :
    (fun j => ((i.firstConditionalLottery htv s hs).point K slot bits j : ℝ)) =
      i.real.firstConditionalDyadicPoint (i.firstCase_real htv) s K slot bits := by
  have hsR := i.interval_real hs
  have he : 0 < i.conditionalProbability s ↔ 0 < i.real.conditionalProbability s := by
    rw [← i.conditionalProbability_real]
    norm_cast
  unfold firstConditionalLottery NestedInput.firstConditionalDyadicPoint
  by_cases hp : 0 < i.conditionalProbability s
  · rw [dite_eq_left hp, dite_eq_left (show (s : ℝ) ∈ i.real.positiveParameters from ⟨hsR, he.mp hp⟩)]
    rw [RationalSegmentLottery.shiftThird_point_real, RationalThreeGeometry.segmentLottery_real, i.firstGeometry_real]
  · have hn : (s : ℝ) ∉ i.real.positiveParameters := fun h => hp (he.mpr h.2)
    rw [dite_eq_right hp, dite_eq_right hn, RationalSegmentLottery.point_real]
    funext j
    fin_cases j <;> simp [RationalSegmentLottery.real, SegmentLottery.dyadicPoint,
      dyadicSegmentPoint, segmentPoint, real]

theorem firstConditionalLottery_point_fullBudget (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) :
    FullBudget (i.M : ℝ) (fun j => ((i.firstConditionalLottery htv s hs).point K slot bits j : ℝ)) := by
  rw [i.firstConditionalLottery_point htv s hs]
  exact i.real.firstConditionalDyadicPoint_fullBudget (i.firstCase_real htv) (i.interval_real hs) K slot bits

theorem firstConditionalLottery_endpoints (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (slot : Fin 9) :
    FullBudget (i.M : ℝ) ((i.firstConditionalLottery htv s hs).real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.firstConditionalLottery htv s hs).real.Q slot) := by
  have hsR := i.interval_real hs
  unfold firstConditionalLottery
  by_cases hp : 0 < i.conditionalProbability s
  · rw [dite_eq_left hp, RationalSegmentLottery.shiftThird_real,
      RationalThreeGeometry.segmentLottery_real, i.firstGeometry_real]
    have hpR : 0 < i.real.conditionalProbability s := by
      rw [← i.conditionalProbability_real]
      exact_mod_cast hp
    let g := i.real.firstGeometry (i.firstCase_real htv) s hsR hpR
    have hB : g.budget + (s : ℝ) = (i.M : ℝ) := by
      have hm := (i.real.firstGeometry_matches (i.firstCase_real htv) s hsR hpR).2.2.2.1
      change g.budget = (i.M : ℝ) - (s : ℝ) at hm
      linarith
    have hP := shiftThird_fullBudget hsR.1 (g.segmentLottery_endpoints.1 slot)
    have hQ := shiftThird_fullBudget hsR.1 (g.segmentLottery_endpoints.2 slot)
    rw [hB] at hP hQ
    exact ⟨hP, hQ⟩
  · rw [dite_eq_right hp]
    have hp0 : i.real.conditionalProbability s = 0 := by
      have hbound := i.conditional_bounds htv hs
      have hn : i.conditionalProbability s = 0 := by linarith
      rw [← i.conditionalProbability_real, hn, Rat.cast_zero]
    have he := i.real.conditional_zero (i.firstCase_real htv) hsR hp0
    dsimp only [real] at he
    have hP : (fun j => ( (![0, i.d, s] : Fin 3 → ℚ) j : ℝ)) = ![0, (i.d : ℝ), (s : ℝ)] := by
      funext j; fin_cases j <;> simp
    have hQ : (fun j => ( (![i.a, 0, s] : Fin 3 → ℚ) j : ℝ)) = ![(i.a : ℝ), 0, (s : ℝ)] := by
      funext j; fin_cases j <;> simp
    change FullBudget (i.M : ℝ) (fun j => ( (![0, i.d, s] : Fin 3 → ℚ) j : ℝ)) ∧
      FullBudget (i.M : ℝ) (fun j => ( (![i.a, 0, s] : Fin 3 → ℚ) j : ℝ))
    rw [hP, hQ]
    exact ⟨fullBudget_three le_rfl (by exact_mod_cast le_of_lt i.d_pos) hsR.1 (by linarith [he.2.2.2]),
      fullBudget_three (by exact_mod_cast le_of_lt i.a_pos) le_rfl hsR.1 (by linarith [he.2.2.1])⟩

theorem firstConditionalLottery_flatLaw_CDF_error (i : RationalNestedInput) (htv : i.t ≤ i.v) (s : ℚ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (K : ℕ) :
    CDFClose ((i.firstConditionalLottery htv s hs).flatLaw 0 (3 * (8 + K)) K)
      (i.real.firstConditionalLaw (i.firstCase_real htv) s) (3 / (2 * (2 : ℝ) ^ K)) := by
  have he := (i.firstConditionalLottery htv s hs).flatLaw_CDF_error 0 K
  rw [i.firstConditionalLottery_law] at he
  exact he

end Blotto.RationalNestedInput
