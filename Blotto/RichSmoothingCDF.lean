import Blotto.RichSmoothingLaw
import Mathlib.Analysis.SpecificLimits.Basic

/-! Scalar CDF limits for the actual rich-player smoothing segments.
The tie limit is derived from the perturbed endpoints, rather than from
weak convergence of laws across a discontinuous payoff. -/

namespace Blotto.RichSmoothingCDF
open MeasureTheory Set Filter
open RichSmoothingGeometry RichSmoothingLaw
open scoped Topology

theorem affineUniform_closedCDF_sorted {a b : ℝ} (hab : a ≠ b) (z : ℝ) :
    (affineUniform a b : Measure ℝ).real (Iic z) =
      max (min z (max a b) - min a b) 0 / (max a b - min a b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · simpa [min_eq_left h.le, max_eq_right h.le] using
      affineUniform_closedCDF_increasing h z
  · simpa [min_eq_right h.le, max_eq_left h.le] using
      affineUniform_closedCDF_decreasing h z

theorem affineUniform_closedCDF_shift_scale (x t a b z : ℝ) (ht : 0 < t) :
    (affineUniform (x + t * a) (x + t * b) : Measure ℝ).real (Iic (x + t * z)) =
      (affineUniform a b : Measure ℝ).real (Iic z) := by
  have he : affineLine (x + t * a) (x + t * b) ⁻¹' Iic (x + t * z) =
      affineLine a b ⁻¹' Iic z := by
    ext u
    simp only [mem_preimage, mem_Iic]
    have hAffine : affineLine (x + t * a) (x + t * b) u = x + t * affineLine a b u := by
      unfold affineLine
      ring
    rw [hAffine]
    constructor <;> intro hle <;> nlinarith
  change (Measure.map _ (unitUniform : Measure ℝ)).real _ =
    (Measure.map _ (unitUniform : Measure ℝ)).real _
  rw [map_measureReal_apply (measurable_affineLine _ _) measurableSet_Iic,
    map_measureReal_apply (measurable_affineLine _ _) measurableSet_Iic, he]

theorem symmetric_cdf_limit {a b : ℕ → ℝ} {d : ℝ} (hd : d ≠ 0)
    (ha : Tendsto a atTop (𝓝 (-d))) (hb : Tendsto b atTop (𝓝 d)) :
    Tendsto (fun k => (affineUniform (a k) (b k) : Measure ℝ).real (Iic 0))
      atTop (𝓝 (1 / 2)) := by
  have hLow := ha.min hb
  have hHigh := ha.max hb
  have hDen : max (-d) d - min (-d) d ≠ 0 := by
    rcases lt_or_gt_of_ne hd with h | h
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      linarith
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      linarith
  have hLimit := ((((tendsto_const_nhds (x := (0 : ℝ))).min hHigh).sub hLow).max
    (tendsto_const_nhds (x := (0 : ℝ)))).div
    (hHigh.sub hLow) hDen
  have hValue : max (min 0 (max (-d) d) - min (-d) d) 0 /
      (max (-d) d - min (-d) d) = (1 / 2 : ℝ) := by
    rcases lt_or_gt_of_ne hd with h | h
    · rw [min_eq_right (by linarith : d ≤ -d), max_eq_left (by linarith : d ≤ -d),
        min_eq_left (by linarith : 0 ≤ -d), max_eq_left (by linarith : 0 ≤ 0 - d)]
      field_simp
      ring
    · rw [min_eq_left (by linarith : -d ≤ d), max_eq_right (by linarith : -d ≤ d),
        min_eq_left h.le, max_eq_left (by linarith : 0 ≤ 0 - -d)]
      field_simp
      ring
  rw [hValue] at hLimit
  apply hLimit.congr'
  have hDistinct := (hHigh.sub hLow).eventually_ne hDen
  filter_upwards [hDistinct] with k hk
  apply (affineUniform_closedCDF_sorted (a := a k) (b := b k) ?_ 0).symm
  intro he
  simp [he] at hk

noncomputable def step {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (k : ℕ) : ℝ :=
  radius x h / ((k : ℝ) + 1)

theorem step_positive {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (k : ℕ) :
    0 < step x h k := div_pos (radius_positive x h) (by positivity)

theorem step_le_radius {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (k : ℕ) :
    step x h k ≤ radius x h := by
  unfold step
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
  nlinarith [radius_positive x h, show (0 : ℝ) ≤ k by positivity]

theorem step_tendsto {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) :
    Tendsto (step x h) atTop (𝓝 0) := by
  have ht := (tendsto_const_nhds (x := radius x h)).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  unfold step
  simpa only [div_eq_mul_inv, mul_zero, one_mul] using ht

theorem tie_cdf_limit {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (j : Fin n) (hd : direction x h j ≠ 0) :
    Tendsto (fun k => closedCDF (law x h (step x h k)) j (x j)) atTop (𝓝 (1 / 2)) := by
  have ht := step_tendsto x h
  have ha : Tendsto (fun k => -direction x h j - step x h k * correction x j)
      atTop (𝓝 (-direction x h j)) := by
    simpa using tendsto_const_nhds.sub (ht.mul_const (correction x j))
  have hb : Tendsto (fun k => direction x h j - 3 * step x h k * correction x j)
      atTop (𝓝 (direction x h j)) := by
    simpa using tendsto_const_nhds.sub ((ht.const_mul 3).mul_const (correction x j))
  apply (symmetric_cdf_limit hd ha hb).congr
  intro k
  unfold closedCDF law
  rw [segmentLaw_marginal]
  have hLower : lower x h (step x h k) j =
      x j + step x h k * (-direction x h j - step x h k * correction x j) := by
    unfold lower
    ring
  have hUpper : upper x h (step x h k) j =
      x j + step x h k * (direction x h j - 3 * step x h k * correction x j) := by
    unfold upper
    ring
  rw [hLower, hUpper]
  simpa using (affineUniform_closedCDF_shift_scale (x j) (step x h k)
    (-direction x h j - step x h k * correction x j)
    (direction x h j - 3 * step x h k * correction x j) 0 (step_positive x h k)).symm

theorem affineUniform_cdf_zero {a b z : ℝ} (hab : a ≠ b) (ha : z < a) (hb : z < b) :
    (affineUniform a b : Measure ℝ).real (Iic z) = 0 := by
  rw [affineUniform_closedCDF_sorted hab]
  have hLow : z < min a b := lt_min ha hb
  have hHigh : z ≤ max a b := ha.le.trans (le_max_left _ _)
  rw [min_eq_left hHigh, max_eq_right (by linarith : z - min a b ≤ 0), zero_div]

theorem affineUniform_cdf_one {a b z : ℝ} (hab : a ≠ b) (ha : a ≤ z) (hb : b ≤ z) :
    (affineUniform a b : Measure ℝ).real (Iic z) = 1 := by
  rw [affineUniform_closedCDF_sorted hab, min_eq_right (max_le ha hb)]
  have hDen : 0 < max a b - min a b := by
    rcases lt_or_gt_of_ne hab with h | h
    · simpa [min_eq_left h.le, max_eq_right h.le] using sub_pos.mpr h
    · simpa [min_eq_right h.le, max_eq_left h.le] using sub_pos.mpr h
  rw [max_eq_left hDen.le, div_self hDen.ne']

theorem lower_tendsto {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (j : Fin n) :
    Tendsto (fun k => lower x h (step x h k) j) atTop (𝓝 (x j)) := by
  have ht := step_tendsto x h
  have hLimit := (tendsto_const_nhds (x := x j)).sub (ht.mul_const (direction x h j))
  simpa [lower] using hLimit.sub ((ht.pow 2).mul_const (correction x j))

theorem upper_tendsto {n : ℕ} (x : Allocation n) (h : (active x).Nonempty) (j : Fin n) :
    Tendsto (fun k => upper x h (step x h k) j) atTop (𝓝 (x j)) := by
  have ht := step_tendsto x h
  have hLimit := (tendsto_const_nhds (x := x j)).add (ht.mul_const (direction x h j))
  simpa [upper] using hLimit.sub (((ht.pow 2).const_mul 3).mul_const (correction x j))

theorem below_cdf_limit {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (hn : 2 ≤ n) (hX : ∀ j, 0 ≤ x j) (j : Fin n) (z : ℝ) (hz : z < x j) :
    Tendsto (fun k => closedCDF (law x h (step x h k)) j z) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(lower_tendsto x h j).eventually_const_lt hz,
    (upper_tendsto x h j).eventually_const_lt hz] with k hLower hUpper
  unfold closedCDF law
  rw [segmentLaw_marginal]
  exact (affineUniform_cdf_zero
    (distinct_endpoints x h hn hX _ (step_positive x h k) (step_le_radius x h k) j)
    hLower hUpper).symm

theorem above_cdf_limit {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (hn : 2 ≤ n) (hX : ∀ j, 0 ≤ x j) (j : Fin n) (z : ℝ) (hz : x j < z) :
    Tendsto (fun k => closedCDF (law x h (step x h k)) j z) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(lower_tendsto x h j).eventually_le_const hz,
    (upper_tendsto x h j).eventually_le_const hz] with k hLower hUpper
  unfold closedCDF law
  rw [segmentLaw_marginal]
  exact (affineUniform_cdf_one
    (distinct_endpoints x h hn hX _ (step_positive x h k) (step_le_radius x h k) j)
    hLower hUpper).symm

theorem zero_cdf {n : ℕ} (x : Allocation n) (h : (active x).Nonempty)
    (hn : 2 ≤ n) (hX : ∀ j, 0 ≤ x j) (j : Fin n) (k : ℕ) :
    closedCDF (law x h (step x h k)) j 0 = 0 := by
  unfold closedCDF law
  rw [segmentLaw_marginal]
  exact affineUniform_cdf_zero
    (distinct_endpoints x h hn hX _ (step_positive x h k) (step_le_radius x h k) j)
    (positive_endpoints x h hn hX _ (step_positive x h k) (step_le_radius x h k) j).1
    (positive_endpoints x h hn hX _ (step_positive x h k) (step_le_radius x h k) j).2

end Blotto.RichSmoothingCDF
