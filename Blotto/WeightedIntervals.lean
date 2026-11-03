import Blotto.UniformInterval

/-! Degeneracy-safe weighted interval laws. A zero-length projection has
zero weight when its mass is length times density; no division by zero is used. -/

namespace Blotto

open MeasureTheory Set

noncomputable def rawInterval (a b : ℝ) : Measure ℝ := volume.restrict (Icc a b)

theorem rawInterval_self (a : ℝ) : rawInterval a a = 0 := by
  apply Measure.restrict_eq_zero.mpr
  simp

theorem rawInterval_glue {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    rawInterval a b + rawInterval b c = rawInterval a c := by
  have hi : Icc a b ∩ Icc b c = {b} := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, h1⟩, ⟨h2, _⟩⟩
      exact le_antisymm h1 h2
    · intro h
      subst t
      exact ⟨⟨hab, le_rfl⟩, ⟨le_rfl, hbc⟩⟩
  have hn : (volume : Measure ℝ).restrict {b} = 0 :=
    Measure.restrict_eq_zero.mpr (measure_singleton b)
  have he := Measure.restrict_union_add_inter (μ := (volume : Measure ℝ))
    (Icc a b) (t := Icc b c) measurableSet_Icc
  rw [Icc_union_Icc_eq_Icc hab hbc, hi, hn, add_zero] at he
  exact he.symm

theorem rawInterval_glue_three {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    rawInterval a b + rawInterval b c + rawInterval c d = rawInterval a d := by
  rw [rawInterval_glue hab hbc, rawInterval_glue (le_trans hab hbc) hcd]

theorem weighted_affine_interval {a b d : ℝ} (hab : a ≤ b) (_hd : 0 ≤ d) :
    ENNReal.ofReal ((b - a) * d) • (affineUniform a b : Measure ℝ) =
      ENNReal.ofReal d • rawInterval a b := by
  rcases eq_or_lt_of_le hab with he | he
  · subst b
    simp [rawInterval_self]
  · have hlen := sub_pos.mpr he
    have h0 := ne_of_gt (ENNReal.ofReal_pos.mpr hlen)
    rw [affineUniform_increasing he, intervalLaw, smul_smul,
      ENNReal.ofReal_mul (le_of_lt hlen)]
    have hs : (ENNReal.ofReal (b - a) * ENNReal.ofReal d) * (ENNReal.ofReal (b - a))⁻¹ =
        ENNReal.ofReal d := by
      calc
        _ = ENNReal.ofReal d * (ENNReal.ofReal (b - a) * (ENNReal.ofReal (b - a))⁻¹) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, mul_one]
    rw [hs]
    rfl

theorem weighted_affine_interval_reverse {a b d : ℝ} (hab : a ≤ b) (hd : 0 ≤ d) :
    ENNReal.ofReal ((b - a) * d) • (affineUniform b a : Measure ℝ) =
      ENNReal.ofReal d • rawInterval a b := by
  rw [affineUniform_reverse b a]
  exact weighted_affine_interval hab hd

theorem affineUniform_scaled_interval {a b q : ℝ} (hab : a < b) (hq : 0 ≤ q) :
    ENNReal.ofReal q • (affineUniform a b : Measure ℝ) =
      ENNReal.ofReal (q / (b - a)) • rawInterval a b := by
  have hd : 0 ≤ q / (b - a) := div_nonneg hq (le_of_lt (sub_pos.mpr hab))
  have he : (b - a) * (q / (b - a)) = q := by
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  simpa only [he] using weighted_affine_interval (le_of_lt hab) hd

theorem affineUniform_scaled_interval_reverse {a b q : ℝ} (hab : a < b) (hq : 0 ≤ q) :
    ENNReal.ofReal q • (affineUniform b a : Measure ℝ) =
      ENNReal.ofReal (q / (b - a)) • rawInterval a b := by
  rw [affineUniform_reverse b a]
  exact affineUniform_scaled_interval hab hq

theorem rawInterval_scaled_glue {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ENNReal.ofReal d • rawInterval a b + ENNReal.ofReal d • rawInterval b c =
      ENNReal.ofReal d • rawInterval a c := by
  rw [← smul_add, rawInterval_glue hab hbc]

theorem rawInterval_scaled_glue_three {a b c d r : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ENNReal.ofReal r • rawInterval a b + ENNReal.ofReal r • rawInterval b c +
      ENNReal.ofReal r • rawInterval c d = ENNReal.ofReal r • rawInterval a d := by
  rw [rawInterval_scaled_glue hab hbc, rawInterval_scaled_glue (le_trans hab hbc) hcd]

end Blotto
