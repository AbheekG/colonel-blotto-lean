import Blotto.NestedFamily

/-! Measure identity F_t = alpha F_T + (1-alpha) Unif[T,t]. The proof
also includes T=t, where the second component has zero mass. -/

namespace Blotto.NestedInput
open MeasureTheory Set

noncomputable def mirrorLength (i : NestedInput) : ℝ := i.u + i.v - i.t
noncomputable def secondAlpha (i : NestedInput) : ℝ :=
  i.mirrorLength * (i.h + i.t) / (i.t * (i.c - i.t))

theorem mirrorLength_bounds (i : NestedInput) (htu : i.u ≤ i.t) :
    0 < i.mirrorLength ∧ i.mirrorLength ≤ i.v ∧ i.mirrorLength ≤ i.t ∧
      i.mirrorLength < i.u + i.v := by
  have hl := i.lengths
  dsimp [mirrorLength]
  constructor <;> try linarith [i.t_pos]
  constructor <;> try linarith [i.t_pos]
  constructor <;> linarith [i.t_pos]

theorem second_beta_identity (i : NestedInput) :
    1 - i.secondAlpha = (i.t - i.mirrorLength) * (i.familyProbability i.t / i.t) := by
  have ht := ne_of_gt i.t_pos
  have hct := ne_of_gt (sub_pos.mpr i.t_lt)
  dsimp [secondAlpha, familyProbability]
  field_simp [ht, hct]
  dsimp [mirrorLength]
  nlinarith [congrArg (fun y : ℝ => y * i.t) i.transformed_balance,
    congrArg (fun y : ℝ => y * i.h) i.transformed_balance]

theorem secondAlpha_bounds (i : NestedInput) (htu : i.u ≤ i.t) :
    0 < i.secondAlpha ∧ i.secondAlpha ≤ 1 := by
  have hT := i.mirrorLength_bounds htu
  have hr : 0 ≤ i.familyProbability i.t / i.t :=
    div_nonneg (le_of_lt (i.familyProbability_bounds i.lengths.2.2.2.1).1) (le_of_lt i.t_pos)
  constructor
  · exact div_pos (mul_pos hT.1 (add_pos i.h_pos i.t_pos)) (mul_pos i.t_pos (sub_pos.mpr i.t_lt))
  · have hbeta := i.second_beta_identity
    have hnonneg := mul_nonneg (sub_nonneg.mpr hT.2.2.1) hr
    linarith

/-- The component densities coincide on [0,T] and on the full [0,c] part. -/
theorem second_component_densities (i : NestedInput) (htu : i.u ≤ i.t) :
    i.secondAlpha * (i.familyProbability i.mirrorLength / i.mirrorLength) =
      i.familyProbability i.t / i.t ∧
    i.secondAlpha * ((1 - i.familyProbability i.mirrorLength) / i.c) =
      (1 - i.familyProbability i.t) / i.c := by
  have hT := i.mirrorLength_bounds htu
  have hTc : i.mirrorLength < i.c := lt_trans hT.2.2.2 i.lengths.2.2.2.2
  have hsum : i.c - i.mirrorLength = i.h + i.t := by
    dsimp [mirrorLength]; linarith [i.transformed_balance]
  have ht := ne_of_gt i.t_pos
  have hc := ne_of_gt i.c_pos
  have hct := ne_of_gt (sub_pos.mpr i.t_lt)
  have hT0 := ne_of_gt hT.1
  have hh := ne_of_gt (add_pos i.h_pos i.t_pos)
  constructor
  · dsimp [secondAlpha, familyProbability]
    rw [hsum]
    field_simp [ht, hc, hct, hT0, hh]
  · dsimp [secondAlpha, familyProbability]
    rw [hsum]
    field_simp [ht, hc, hct, hT0, hh]
    dsimp [mirrorLength]
    nlinarith [congrArg (fun y : ℝ => y * i.t) i.transformed_balance]

theorem second_decomposition (i : NestedInput) (htu : i.u ≤ i.t) :
    i.nestedTargetLaw = ENNReal.ofReal i.secondAlpha • i.familyLaw i.mirrorLength +
      ENNReal.ofReal (1 - i.secondAlpha) • (affineUniform i.mirrorLength i.t : Measure ℝ) := by
  have hT := i.mirrorLength_bounds htu
  have hp := i.familyProbability_bounds i.lengths.2.2.2.1
  have hpT := i.familyProbability_bounds hT.2.2.2
  have hα := i.secondAlpha_bounds htu
  let lo : ℝ := i.familyProbability i.t / i.t
  let hi : ℝ := (1 - i.familyProbability i.t) / i.c
  have hlo : 0 ≤ lo := div_nonneg (le_of_lt hp.1) (le_of_lt i.t_pos)
  have hhi : 0 ≤ hi := div_nonneg (sub_nonneg.mpr (le_of_lt hp.2)) (le_of_lt i.c_pos)
  have hloT : 0 ≤ i.familyProbability i.mirrorLength / i.mirrorLength :=
    div_nonneg (le_of_lt hpT.1) (le_of_lt hT.1)
  have hhiT : 0 ≤ (1 - i.familyProbability i.mirrorLength) / i.c :=
    div_nonneg (sub_nonneg.mpr (le_of_lt hpT.2)) (le_of_lt i.c_pos)
  have he := i.second_component_densities htu
  have hb := i.second_beta_identity
  rw [← i.familyLaw_original, i.familyLaw_density i.t_pos i.lengths.2.2.2.1,
    i.familyLaw_density hT.1 hT.2.2.2, smul_add, smul_smul, smul_smul,
    ← ENNReal.ofReal_mul (le_of_lt hα.1), ← ENNReal.ofReal_mul (le_of_lt hα.1),
    he.1, he.2, hb, weighted_affine_interval hT.2.2.1 hlo]
  change ENNReal.ofReal lo • rawInterval 0 i.t + ENNReal.ofReal hi • rawInterval 0 i.c =
    (ENNReal.ofReal lo • rawInterval 0 i.mirrorLength + ENNReal.ofReal hi • rawInterval 0 i.c) +
      ENNReal.ofReal lo • rawInterval i.mirrorLength i.t
  rw [← rawInterval_scaled_glue (le_of_lt hT.1) hT.2.2.1]
  simp only [add_assoc, add_comm]

end Blotto.NestedInput
