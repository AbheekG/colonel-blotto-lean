import Blotto.InitialSegmentCount
import Blotto.FiniteUniformPoints

/-! The midpoint-grid primitive: exact finite law and its dimension-free
Kolmogorov discrepancy from the unit uniform. Fair-bit generation is separate. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def midpoint {N : ℕ} (j : Fin N) : ℝ := ((j.val : ℝ) + 1 / 2) / N

theorem midpoint_bounds {N : ℕ} (hN : 0 < N) (j : Fin N) : 0 < midpoint j ∧ midpoint j < 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hj : (j.val : ℝ) < N := by exact_mod_cast j.isLt
  constructor
  · exact div_pos (by positivity) hNr
  · apply (div_lt_one hNr).mpr
    have hjs : j.val + 1 ≤ N := j.isLt
    have hjr : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast hjs
    linarith

theorem midpoint_monotone {N : ℕ} (hN : 0 < N) : Monotone (@midpoint N) := by
  intro i j hij
  unfold midpoint
  apply div_le_div_of_nonneg_right
  · have h : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij
    linarith
  · positivity

noncomputable def midpointLaw {N : ℕ} (hN : 0 < N) : ProbabilityMeasure ℝ :=
  finiteUniformPoints hN midpoint

theorem midpointLaw_supported {N : ℕ} (hN : 0 < N) :
    ∀ᵐ x ∂(midpointLaw hN : Measure ℝ), x ∈ Icc 0 1 :=
  finiteUniformPoints_supported hN midpoint (fun j => ⟨le_of_lt (midpoint_bounds hN j).1, le_of_lt (midpoint_bounds hN j).2⟩)

theorem midpointLaw_closedCDF {N : ℕ} (hN : 0 < N) (z : ℝ) :
    (midpointLaw hN : Measure ℝ).real (Iic z) =
      (∑ j : Fin N, if midpoint j ≤ z then (1 : ℝ) else 0) / N :=
  finiteUniformPoints_event hN midpoint (Iic z) measurableSet_Iic

theorem midpoint_count_discrepancy {N : ℕ} (hN : 0 < N) (z : ℝ) :
    |((∑ j : Fin N, if midpoint j ≤ z then (1 : ℝ) else 0) / N) - max (min z 1) 0| ≤ 1 / (2 * (N : ℝ)) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have herror : 0 ≤ 1 / (2 * (N : ℝ)) := by positivity
  by_cases hz0 : z < 0
  · have hnone : ∀ j : Fin N, ¬midpoint j ≤ z := fun j h => not_lt_of_ge h (lt_trans hz0 (midpoint_bounds hN j).1)
    simp only [hnone, ite_false, Finset.sum_const_zero, zero_div,
      min_eq_left (by linarith : z ≤ 1), max_eq_right (le_of_lt hz0), sub_self, abs_zero]
    exact herror
  have hz : 0 ≤ z := le_of_not_gt hz0
  by_cases hz1 : 1 < z
  · have hall : ∀ j : Fin N, midpoint j ≤ z := fun j => (le_of_lt (midpoint_bounds hN j).2).trans (le_of_lt hz1)
    simp only [hall, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, div_self (ne_of_gt hNr), min_eq_right (le_of_lt hz1),
      max_eq_left (by norm_num : (0 : ℝ) ≤ 1), sub_self, abs_zero]
    exact herror
  have hz' : z ≤ 1 := le_of_not_gt hz1
  rcases initialSegment_count (fun j : Fin N => midpoint j ≤ z)
    (fun i j hij hj => (midpoint_monotone hN hij).trans hj) with ⟨k, hkN, hk, hsum⟩
  have hsumR : (∑ j : Fin N, if midpoint j ≤ z then (1 : ℝ) else 0) = (k : ℝ) := by
    exact_mod_cast hsum
  rw [hsumR, min_eq_left hz', max_eq_left hz]
  apply abs_le.mpr
  constructor
  · by_cases he : k = N
    · rw [he, div_self (ne_of_gt hNr)]
      linarith
    · have hklt : k < N := lt_of_le_of_ne hkN he
      let j : Fin N := ⟨k, hklt⟩
      have hn : ¬midpoint j ≤ z := fun h => (Nat.lt_irrefl k) ((hk j).mp h)
      have hlt : z < ((k : ℝ) + 1 / 2) / N := lt_of_not_ge hn
      have hs : z * N < (k : ℝ) + 1 / 2 := (lt_div_iff₀ hNr).mp hlt
      have heq : 1 / (2 * (N : ℝ)) = (1 / 2 : ℝ) / N := by field_simp
      rw [heq]
      have ht : z - (k : ℝ) / N ≤ (1 / 2 : ℝ) / N := by
        apply (le_div_iff₀ hNr).mpr
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hNr)]
        linarith
      linarith
  · by_cases he : k = 0
    · simp only [he, Nat.cast_zero, zero_div, zero_sub]
      linarith
    · have hkpos : 0 < k := Nat.pos_of_ne_zero he
      let j : Fin N := ⟨k - 1, by omega⟩
      have hj : midpoint j ≤ z := (hk j).mpr (by dsimp [j]; omega)
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have hs : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast (Nat.sub_add_cancel hkpos)
        linarith
      have hs : (k : ℝ) - 1 + 1 / 2 ≤ z * N := by
        change (((k - 1 : ℕ) : ℝ) + 1 / 2) / N ≤ z at hj
        rw [hcast] at hj
        exact (div_le_iff₀ hNr).mp hj
      have heq : 1 / (2 * (N : ℝ)) = (1 / 2 : ℝ) / N := by field_simp
      rw [heq]
      have ht : (k : ℝ) / N ≤ z + (1 / 2 : ℝ) / N := by
        apply (div_le_iff₀ hNr).mpr
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hNr)]
        linarith
      linarith

theorem midpointLaw_CDF_error {N : ℕ} (hN : 0 < N) (z : ℝ) :
    |(midpointLaw hN : Measure ℝ).real (Iic z) - (unitUniform : Measure ℝ).real (Iic z)| ≤ 1 / (2 * (N : ℝ)) := by
  rw [midpointLaw_closedCDF, unitUniform_closedCDF]
  exact midpoint_count_discrepancy hN z

end Blotto
