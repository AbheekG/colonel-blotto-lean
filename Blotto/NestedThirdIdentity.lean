import Blotto.NestedFamily

/-! The middle nested case: cancellation of the low interval and the exact
translated residual measure, including v=0. -/

namespace Blotto.NestedInput
open MeasureTheory Set

noncomputable def thirdAlpha (i : NestedInput) : ℝ :=
  i.v * (i.h + i.t) / (i.t * (i.h + i.v))

theorem thirdAlpha_bounds (i : NestedInput) (hv : 0 < i.v) (hvt : i.v < i.t) :
    0 < i.thirdAlpha ∧ i.thirdAlpha < 1 := by
  have hh := i.h_pos
  have ht := i.t_pos
  have hden : 0 < i.t * (i.h + i.v) := mul_pos ht (add_pos hh hv)
  constructor
  · exact div_pos (mul_pos hv (add_pos hh ht)) hden
  · apply (div_lt_one hden).mpr
    nlinarith [mul_pos hh (sub_pos.mpr hvt)]

theorem residual_zero_target (i : NestedInput) (hv : i.v = 0) (hvt : i.v < i.t) (htu : i.t < i.u) :
    (i.residualInput hvt htu).targetLaw = i.nestedTargetLaw := by
  have hc := i.geometry_matches.2.2.1
  have hp : i.familyProbability i.t = i.q := by
    dsimp [familyProbability, h]
    field_simp [ne_of_gt (sub_pos.mpr i.t_lt)]
  have he : (i.residualInput hvt htu).alpha = i.q := by
    change (i.v + i.h) / (i.geometry.c - i.t) = i.q
    rw [hc, hv, zero_add]
    exact hp
  have hx : ∀ {a : ℝ}, 0 < a → (affineUniform 0 a : Measure ℝ) = uniformLaw a := by
    intro a ha
    rw [affineUniform_increasing ha]
    simp only [intervalLaw, sub_zero, uniformLaw]
  rw [NestedResidual.targetLaw, he]
  change ENNReal.ofReal i.q • (affineUniform i.v i.t : Measure ℝ) +
    ENNReal.ofReal (1 - i.q) • (affineUniform i.v i.geometry.c : Measure ℝ) = _
  rw [hv, hc, hx i.t_pos, hx i.c_pos]
  rfl

theorem third_decomposition (i : NestedInput) (hv : 0 < i.v)
    (hvt : i.v < i.t) (htu : i.t < i.u) :
    i.nestedTargetLaw = ENNReal.ofReal i.thirdAlpha • i.familyLaw i.v +
      ENNReal.ofReal (1 - i.thirdAlpha) • (i.residualInput hvt htu).targetLaw := by
  have hα := i.thirdAlpha_bounds hv hvt
  have hq := i.familyProbability_bounds i.lengths.2.2.2.1
  have hvsum : i.v < i.u + i.v := by linarith [i.lengths.2.2.1]
  have hqv := i.familyProbability_bounds hvsum
  have hct : 0 < i.c - i.t := sub_pos.mpr i.t_lt
  have hcv : 0 < i.c - i.v := sub_pos.mpr (lt_trans hvt i.t_lt)
  have htv : 0 < i.t - i.v := sub_pos.mpr hvt
  let β : ℝ := (i.residualInput hvt htu).alpha
  have hβ : 0 ≤ β ∧ β ≤ 1 := ⟨le_of_lt (i.residualInput hvt htu).alpha_bounds.1,
    le_of_lt (i.residualInput hvt htu).alpha_bounds.2⟩
  have hβeq : β = (i.v + i.h) / (i.c - i.t) := by
    change (i.geometry.G / (i.geometry.c - i.t)) = _
    rw [i.geometry_matches.2.2.1]
    rfl
  let a : ℝ := i.familyProbability i.t / i.t
  let b : ℝ := (1 - i.familyProbability i.t) / i.c
  let f : ℝ := i.thirdAlpha * (i.familyProbability i.v / i.v)
  let g : ℝ := i.thirdAlpha * ((1 - i.familyProbability i.v) / i.c)
  let r : ℝ := (1 - i.thirdAlpha) * (β / (i.t - i.v))
  let s : ℝ := (1 - i.thirdAlpha) * ((1 - β) / (i.c - i.v))
  have ha : 0 ≤ a := div_nonneg (le_of_lt hq.1) (le_of_lt i.t_pos)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr (le_of_lt hq.2)) (le_of_lt i.c_pos)
  have hf : 0 ≤ f := mul_nonneg (le_of_lt hα.1) (div_nonneg (le_of_lt hqv.1) (le_of_lt hv))
  have hg : 0 ≤ g := mul_nonneg (le_of_lt hα.1)
    (div_nonneg (sub_nonneg.mpr (le_of_lt hqv.2)) (le_of_lt i.c_pos))
  have hr : 0 ≤ r := mul_nonneg (sub_nonneg.mpr (le_of_lt hα.2)) (div_nonneg hβ.1 (le_of_lt htv))
  have hs : 0 ≤ s := mul_nonneg (sub_nonneg.mpr (le_of_lt hα.2))
    (div_nonneg (sub_nonneg.mpr hβ.2) (le_of_lt hcv))
  have htlo : a + b = f + g := by
    dsimp [a, b, f, g, thirdAlpha, familyProbability]
    field_simp [ne_of_gt hv, ne_of_gt i.t_pos, ne_of_gt i.c_pos,
      ne_of_gt hct, ne_of_gt hcv, ne_of_gt (add_pos i.h_pos hv)]
    ring
  have htmid : a + b = g + r + s := by
    dsimp [a, b, g, r, s, thirdAlpha, familyProbability]
    rw [hβeq]
    field_simp [ne_of_gt hv, ne_of_gt i.t_pos, ne_of_gt i.c_pos,
      ne_of_gt hct, ne_of_gt hcv, ne_of_gt htv, ne_of_gt (add_pos i.h_pos hv)]
    ring
  have hthi : b = g + s := by
    dsimp [b, g, s, thirdAlpha, familyProbability]
    rw [hβeq]
    field_simp [ne_of_gt i.t_pos, ne_of_gt i.c_pos, ne_of_gt hct,
      ne_of_gt hcv, ne_of_gt (add_pos i.h_pos hv)]
    ring
  have hl : rawInterval 0 i.t = rawInterval 0 i.v + rawInterval i.v i.t :=
    (rawInterval_glue (le_of_lt hv) (le_of_lt hvt)).symm
  have hh : rawInterval 0 i.c = rawInterval 0 i.v + rawInterval i.v i.t + rawInterval i.t i.c :=
    (rawInterval_glue_three (le_of_lt hv) (le_of_lt hvt) (le_of_lt i.t_lt)).symm
  have hm : rawInterval i.v i.c = rawInterval i.v i.t + rawInterval i.t i.c :=
    (rawInterval_glue (le_of_lt hvt) (le_of_lt i.t_lt)).symm
  rw [← i.familyLaw_original, i.familyLaw_density i.t_pos i.lengths.2.2.2.1,
    i.familyLaw_density hv hvsum, NestedResidual.targetLaw]
  change ENNReal.ofReal a • rawInterval 0 i.t + ENNReal.ofReal b • rawInterval 0 i.c =
    ENNReal.ofReal i.thirdAlpha •
      (ENNReal.ofReal (i.familyProbability i.v / i.v) • rawInterval 0 i.v +
        ENNReal.ofReal ((1 - i.familyProbability i.v) / i.c) • rawInterval 0 i.c) +
    ENNReal.ofReal (1 - i.thirdAlpha) •
      (ENNReal.ofReal β • (affineUniform i.v i.t : Measure ℝ) +
        ENNReal.ofReal (1 - β) • (affineUniform i.v i.geometry.c : Measure ℝ))
  rw [i.geometry_matches.2.2.1, affineUniform_scaled_interval hvt hβ.1,
    affineUniform_scaled_interval (sub_pos.mp hcv) (sub_nonneg.mpr hβ.2),
    smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
    ← ENNReal.ofReal_mul (le_of_lt hα.1), ← ENNReal.ofReal_mul (le_of_lt hα.1),
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (le_of_lt hα.2)),
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (le_of_lt hα.2))]
  change ENNReal.ofReal a • rawInterval 0 i.t + ENNReal.ofReal b • rawInterval 0 i.c =
    (ENNReal.ofReal f • rawInterval 0 i.v + ENNReal.ofReal g • rawInterval 0 i.c) +
      (ENNReal.ofReal r • rawInterval i.v i.t + ENNReal.ofReal s • rawInterval i.v i.c)
  calc
    _ = ENNReal.ofReal (a + b) • rawInterval 0 i.v +
      ENNReal.ofReal (a + b) • rawInterval i.v i.t + ENNReal.ofReal b • rawInterval i.t i.c := by
      rw [hl, hh, ofReal_smul_add ha hb, ofReal_smul_add ha hb]
      simp only [smul_add, add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal (f + g) • rawInterval 0 i.v +
      ENNReal.ofReal (g + r + s) • rawInterval i.v i.t +
        ENNReal.ofReal (g + s) • rawInterval i.t i.c := by
      rw [congrArg (fun x : ℝ => ENNReal.ofReal x • rawInterval 0 i.v) htlo,
        congrArg (fun x : ℝ => ENNReal.ofReal x • rawInterval i.v i.t) htmid,
        congrArg (fun x : ℝ => ENNReal.ofReal x • rawInterval i.t i.c) hthi]
    _ = _ := by
      rw [hh, hm, ofReal_smul_add hf hg,
        ofReal_smul_add (add_nonneg hg hr) hs, ofReal_smul_add hg hr, ofReal_smul_add hg hs]
      simp only [smul_add]
      generalize ENNReal.ofReal f = F
      generalize ENNReal.ofReal g = G
      generalize ENNReal.ofReal r = R
      generalize ENNReal.ofReal s = S
      generalize rawInterval 0 i.v = μ0
      generalize rawInterval i.v i.t = μ1
      generalize rawInterval i.t i.c = μ2
      simp only [add_assoc, add_left_comm]

end Blotto.NestedInput
