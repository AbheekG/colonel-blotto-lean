import Blotto.NestedConditional
import Blotto.MonotoneExpectation

/-! The first nested conditional CDF is an increasing clipped function minus
one increasing step, both taking values in [0,1]. This gives the manuscript's
variation-at-most-two bound without discarding its atom at the cutoff. -/

namespace Blotto.NestedInput
open MeasureTheory Set

theorem conditionalCDF_monotoneOn (i : NestedInput) {z : ℝ} (_hz0 : 0 ≤ z) (hzc : z ≤ i.c) :
    MonotoneOn (fun s => i.conditionalCDF s z) (Icc 0 (min z i.t)) := by
  intro x hx y hy hxy
  have hxz : x ≤ z := hx.2.trans (min_le_left _ _)
  have hyz : y ≤ z := hy.2.trans (min_le_left _ _)
  have hxc : 0 < i.c - x := by linarith [i.t_lt, hx.2.trans (min_le_right z i.t)]
  have hyc : 0 < i.c - y := by linarith [i.t_lt, hy.2.trans (min_le_right z i.t)]
  have he : i.conditionalCDF y z - i.conditionalCDF x z =
      (i.c - z) * (y - x) * ((i.h + x) * (i.c - y) + (i.h + y) * (i.c - x)) /
        ((i.c - y) ^ 2 * (i.c - x) ^ 2) := by
    rw [conditionalCDF, ite_eq_left hyz, conditionalCDF, ite_eq_left hxz]
    field_simp [ne_of_gt hxc, ne_of_gt hyc]
    ring
  apply sub_nonneg.mp
  rw [he]
  apply div_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hzc) (sub_nonneg.mpr hxy)
    · exact add_nonneg
        (mul_nonneg (le_of_lt (add_pos_of_pos_of_nonneg i.h_pos hx.1)) (le_of_lt hyc))
        (mul_nonneg (le_of_lt (add_pos_of_pos_of_nonneg i.h_pos hy.1)) (le_of_lt hxc))
  · positivity

noncomputable def cdfClip (i : NestedInput) (z s : ℝ) : ℝ := max (min s (min z i.t)) 0

theorem cdfClip_bounds (i : NestedInput) {z : ℝ} (hz0 : 0 ≤ z) (s : ℝ) :
    i.cdfClip z s ∈ Icc 0 (min z i.t) := by
  have hb : 0 ≤ min z i.t := le_min hz0 (le_of_lt i.t_pos)
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) hb⟩

noncomputable def clippedCDF (i : NestedInput) (z s : ℝ) : ℝ := i.conditionalCDF (i.cdfClip z s) z
noncomputable def cutoffCDF (i : NestedInput) (z s : ℝ) : ℝ :=
  if z < s then i.conditionalCDF (min z i.t) z else 0

theorem clippedCDF_monotone (i : NestedInput) {z : ℝ} (hz0 : 0 ≤ z) (hzc : z ≤ i.c) :
    Monotone (i.clippedCDF z) := by
  intro x y hxy
  apply i.conditionalCDF_monotoneOn hz0 hzc (i.cdfClip_bounds hz0 x) (i.cdfClip_bounds hz0 y)
  exact max_le_max (min_le_min hxy le_rfl) le_rfl

theorem clippedCDF_bounds (i : NestedInput) (htv : i.t ≤ i.v) {z : ℝ}
    (hz0 : 0 ≤ z) (hzc : z ≤ i.c) (s : ℝ) : 0 ≤ i.clippedCDF z s ∧ i.clippedCDF z s ≤ 1 := by
  have hb := i.cdfClip_bounds hz0 s
  exact i.conditionalCDF_bounds htv ⟨hb.1, hb.2.trans (min_le_right _ _)⟩ hzc

theorem cutoffCDF_monotone (i : NestedInput) (htv : i.t ≤ i.v) {z : ℝ}
    (hz0 : 0 ≤ z) (hzc : z ≤ i.c) : Monotone (i.cutoffCDF z) := by
  have hb := i.conditionalCDF_bounds htv ⟨le_min hz0 (le_of_lt i.t_pos), min_le_right _ _⟩ hzc
  intro x y hxy
  unfold cutoffCDF
  split_ifs <;> linarith [hb.1]

theorem cutoffCDF_bounds (i : NestedInput) (htv : i.t ≤ i.v) {z : ℝ}
    (hz0 : 0 ≤ z) (hzc : z ≤ i.c) (s : ℝ) : 0 ≤ i.cutoffCDF z s ∧ i.cutoffCDF z s ≤ 1 := by
  have hb := i.conditionalCDF_bounds htv ⟨le_min hz0 (le_of_lt i.t_pos), min_le_right _ _⟩ hzc
  unfold cutoffCDF
  split_ifs
  · exact hb
  · norm_num

theorem conditionalCDF_decomposition (i : NestedInput) {z s : ℝ} (hz0 : 0 ≤ z)
    (hs : s ∈ Icc 0 i.t) :
    i.conditionalCDF s z = i.clippedCDF z s - i.cutoffCDF z s := by
  by_cases hsz : s ≤ z
  · have hsb : s ≤ min z i.t := le_min hsz hs.2
    simp [clippedCDF, cdfClip, cutoffCDF, min_eq_left hsb, max_eq_left hs.1, not_lt.mpr hsz]
  · have hzs : z < s := lt_of_not_ge hsz
    have hzt : z ≤ i.t := (le_of_lt hzs).trans hs.2
    simp [conditionalCDF, clippedCDF, cdfClip, cutoffCDF, hsz, hzs,
      min_eq_left hzt, min_eq_right (le_of_lt hzs), max_eq_left hz0]

theorem conditionalCDF_expectation_error (i : NestedInput) (htv : i.t ≤ i.v)
    (ρ σ : ProbabilityMeasure ℝ) {δ z : ℝ} (hc : RealCDFClose ρ σ δ)
    (hρ : ∀ᵐ s ∂(ρ : Measure ℝ), s ∈ Icc 0 i.t)
    (hσ : ∀ᵐ s ∂(σ : Measure ℝ), s ∈ Icc 0 i.t) (hzc : z ≤ i.c) :
    |(∫ s, i.conditionalCDF s z ∂(ρ : Measure ℝ)) -
      (∫ s, i.conditionalCDF s z ∂(σ : Measure ℝ))| ≤ 2 * δ := by
  by_cases hz : z < 0
  · have heρ : (fun s => i.conditionalCDF s z) =ᵐ[(ρ : Measure ℝ)] (fun _ => 0) :=
      hρ.mono (fun s hs => by simp [conditionalCDF, not_le.mpr (lt_of_lt_of_le hz hs.1)])
    have heσ : (fun s => i.conditionalCDF s z) =ᵐ[(σ : Measure ℝ)] (fun _ => 0) :=
      hσ.mono (fun s hs => by simp [conditionalCDF, not_le.mpr (lt_of_lt_of_le hz hs.1)])
    rw [integral_congr_ae heρ, integral_congr_ae heσ, integral_zero, integral_zero]
    simpa only [sub_self, abs_zero] using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc.nonnegative)
  · have hz0 := le_of_not_gt hz
    exact hc.difference_integral (fun s => i.conditionalCDF s z) (i.clippedCDF z) (i.cutoffCDF z)
      (i.clippedCDF_monotone hz0 hzc) (i.cutoffCDF_monotone htv hz0 hzc)
      (i.clippedCDF_bounds htv hz0 hzc) (i.cutoffCDF_bounds htv hz0 hzc)
      (hρ.mono (fun _ hs => i.conditionalCDF_decomposition hz0 hs))
      (hσ.mono (fun _ hs => i.conditionalCDF_decomposition hz0 hs))

end Blotto.NestedInput
