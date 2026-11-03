import Blotto.NestedLocation

/-! The three-segment residual coupling in the middle case of Lemma 2.3.
This law is proved independently of the first-case averaging. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

structure NestedResidual where
  g : ThreeGeometry
  t : ℝ
  h_pos : 0 < g.h
  v_lt : g.v < t
  lt_u : t < g.u

namespace NestedResidual

noncomputable def s (r : NestedResidual) : ℝ := r.g.u - r.t
noncomputable def K (r : NestedResidual) : ℝ := r.g.G * r.g.d + r.g.w * r.s
noncomputable def alpha (r : NestedResidual) : ℝ := r.g.G / (r.g.c - r.t)

noncomputable def weight (r : NestedResidual) : Fin 3 → ℝ :=
  ![r.g.w * r.s / r.K, r.g.G * (r.g.d - r.s) / r.K, r.g.G * r.s / r.K]

noncomputable def vertex (r : NestedResidual) : Fin 3 → Allocation 3 :=
  ![![0, r.g.d, r.g.v], ![r.g.w, 0, r.g.c], ![r.g.a, r.s, r.t]]

noncomputable def edges : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

theorem parameters (r : NestedResidual) :
    0 < r.s ∧ 0 < r.g.G ∧ 0 < r.g.c - r.t ∧ 0 < r.g.d - r.s ∧ 0 < r.K := by
  have hu := r.g.u_pos
  have hv := r.g.v_nonneg
  have hw := r.g.w_nonneg
  have hh := r.h_pos
  have hs : 0 < r.s := sub_pos.mpr r.lt_u
  have hG : 0 < r.g.G := add_pos_of_nonneg_of_pos hv hh
  have hct : 0 < r.g.c - r.t := by dsimp [ThreeGeometry.c]; linarith [r.lt_u]
  have hds : 0 < r.g.d - r.s := by dsimp [ThreeGeometry.d, s]; linarith [r.v_lt]
  have hK : 0 < r.K := add_pos_of_pos_of_nonneg
    (mul_pos hG r.g.lengths_positive.2.1) (mul_nonneg hw (le_of_lt hs))
  exact ⟨hs, hG, hct, hds, hK⟩

theorem alpha_bounds (r : NestedResidual) : 0 < r.alpha ∧ r.alpha < 1 := by
  have hp := r.parameters
  constructor
  · exact div_pos hp.2.1 hp.2.2.1
  · apply (div_lt_one hp.2.2.1).mpr
    dsimp [ThreeGeometry.G, ThreeGeometry.c]
    linarith [r.lt_u]

theorem weight_nonnegative (r : NestedResidual) : ∀ i, 0 ≤ r.weight i := by
  have hp := r.parameters
  have hs := hp.1
  have hG := hp.2.1
  have hds := hp.2.2.2.1
  have hK := hp.2.2.2.2
  have hw := r.g.w_nonneg
  intro i
  fin_cases i <;> simp [weight]
  all_goals positivity

theorem weight_mass (r : NestedResidual) : ∑ i, r.weight i = 1 := by
  simp [weight, Fin.sum_univ_succ]
  field_simp [ne_of_gt r.parameters.2.2.2.2]
  dsimp [K]
  ring

theorem vertex_fullBudget (r : NestedResidual) (i : Fin 3) :
    FullBudget r.g.budget (r.vertex i) := by
  fin_cases i
  · apply fullBudget_three (le_refl 0) (le_of_lt r.g.lengths_positive.2.1) r.g.v_nonneg
    dsimp [ThreeGeometry.d, ThreeGeometry.budget]; ring
  · apply fullBudget_three r.g.w_nonneg (le_refl 0) (le_of_lt r.g.lengths_positive.2.2.1)
    dsimp [ThreeGeometry.c, ThreeGeometry.budget]; ring
  · apply fullBudget_three (le_of_lt r.g.lengths_positive.1) (le_of_lt r.parameters.1)
      (le_of_lt (lt_of_le_of_lt r.g.v_nonneg r.v_lt))
    dsimp [ThreeGeometry.a, ThreeGeometry.budget, s]; ring

noncomputable def edgeLaw (r : NestedResidual) (i : Fin 3) : Mixed 3 :=
  segmentLaw (r.vertex (edges i).1) (r.vertex (edges i).2)

noncomputable def law (r : NestedResidual) : Mixed 3 :=
  probabilityMixture r.weight r.edgeLaw r.weight_nonnegative r.weight_mass

theorem law_fullBudget (r : NestedResidual) :
    ∀ᵐ x ∂(r.law : Measure (Allocation 3)), FullBudget r.g.budget x := by
  apply probabilityMixture_ae
  intro i
  exact segmentLaw_fullBudget (r.vertex_fullBudget _) (r.vertex_fullBudget _)

theorem law_marginal (r : NestedResidual) (j : Fin 3) :
    (marginal r.law j : Measure ℝ) =
      ∑ i, ENNReal.ofReal (r.weight i) •
        (affineUniform (r.vertex (edges i).1 j) (r.vertex (edges i).2 j) : Measure ℝ) := by
  rw [law, probabilityMixture_marginal, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [edgeLaw, segmentLaw_marginal]

theorem law_marginal_x (r : NestedResidual) :
    (marginal r.law 0 : Measure ℝ) = uniformLaw r.g.a := by
  have hp := r.parameters
  have ha := r.g.lengths_positive.1
  let d : ℝ := r.s / r.K
  let e : ℝ := r.g.G * (r.g.d - r.s) / r.K / r.g.a
  have hd : 0 ≤ d := le_of_lt (div_pos hp.1 hp.2.2.2.2)
  have he : 0 ≤ e := div_nonneg
    (div_nonneg (mul_nonneg (le_of_lt hp.2.1) (le_of_lt hp.2.2.2.1))
      (le_of_lt hp.2.2.2.2)) (le_of_lt ha)
  have hwa : r.g.w ≤ r.g.a := by dsimp [ThreeGeometry.a]; linarith [r.g.v_nonneg, r.h_pos]
  have h0 : r.weight 0 = (r.g.w - 0) * d := by dsimp [weight, d]; ring
  have h1 : r.weight 1 = (r.g.a - 0) * e := by
    dsimp [weight, e]; field_simp [ne_of_gt ha]; ring
  have h2 : r.weight 2 = (r.g.a - r.g.w) * d := by
    dsimp [weight, d, ThreeGeometry.a, ThreeGeometry.G]; ring
  have ht : d + e = 1 / r.g.a := by
    dsimp [d, e]
    field_simp [ne_of_gt ha, ne_of_gt hp.2.2.2.2]
    dsimp [K, ThreeGeometry.a, ThreeGeometry.G]
    ring
  rw [r.law_marginal]
  simp [vertex, edges, Fin.sum_univ_succ]
  rw [h0, h1, h2, weighted_affine_interval r.g.w_nonneg hd,
    weighted_affine_interval (le_of_lt ha) he, weighted_affine_interval hwa hd]
  calc
    _ = (ENNReal.ofReal d • rawInterval 0 r.g.w + ENNReal.ofReal d • rawInterval r.g.w r.g.a) +
        ENNReal.ofReal e • rawInterval 0 r.g.a := by
      simp only [add_assoc, add_comm]
    _ = ENNReal.ofReal (d + e) • rawInterval 0 r.g.a := by
      rw [rawInterval_scaled_glue r.g.w_nonneg hwa, ofReal_smul_add hd he]
    _ = uniformLaw r.g.a := by rw [ht, ← uniformLaw_density ha]

theorem law_marginal_y (r : NestedResidual) :
    (marginal r.law 1 : Measure ℝ) = uniformLaw r.g.d := by
  have hp := r.parameters
  have hD := r.g.lengths_positive.2.1
  let d : ℝ := r.g.G / r.K
  let e : ℝ := r.g.w * r.s / r.K / r.g.d
  have hd : 0 ≤ d := le_of_lt (div_pos hp.2.1 hp.2.2.2.2)
  have he : 0 ≤ e := div_nonneg
    (div_nonneg (mul_nonneg r.g.w_nonneg (le_of_lt hp.1))
      (le_of_lt hp.2.2.2.2)) (le_of_lt hD)
  have hsd : r.s ≤ r.g.d := by linarith [hp.2.2.2.1]
  have h0 : r.weight 0 = (r.g.d - 0) * e := by
    dsimp [weight, e]; field_simp [ne_of_gt hD]; ring
  have h1 : r.weight 1 = (r.g.d - r.s) * d := by dsimp [weight, d]; ring
  have h2 : r.weight 2 = (r.s - 0) * d := by dsimp [weight, d]; ring
  have ht : d + e = 1 / r.g.d := by
    dsimp [d, e]
    field_simp [ne_of_gt hD, ne_of_gt hp.2.2.2.2]
    dsimp [K]
  rw [r.law_marginal]
  simp [vertex, edges, Fin.sum_univ_succ]
  rw [h0, h1, h2, weighted_affine_interval_reverse (le_of_lt hD) he,
    weighted_affine_interval_reverse hsd hd, weighted_affine_interval (le_of_lt hp.1) hd]
  calc
    _ = (ENNReal.ofReal d • rawInterval 0 r.s + ENNReal.ofReal d • rawInterval r.s r.g.d) +
        ENNReal.ofReal e • rawInterval 0 r.g.d := by
      simp only [add_assoc, add_comm]
    _ = ENNReal.ofReal (d + e) • rawInterval 0 r.g.d := by
      rw [rawInterval_scaled_glue (le_of_lt hp.1) hsd, ofReal_smul_add hd he]
    _ = uniformLaw r.g.d := by rw [ht, ← uniformLaw_density hD]

noncomputable def targetLaw (r : NestedResidual) : Measure ℝ :=
  ENNReal.ofReal r.alpha • (affineUniform r.g.v r.t : Measure ℝ) +
    ENNReal.ofReal (1 - r.alpha) • (affineUniform r.g.v r.g.c : Measure ℝ)

theorem law_marginal_z (r : NestedResidual) :
    (marginal r.law 2 : Measure ℝ) = r.targetLaw := by
  have hp := r.parameters
  have ha := r.g.lengths_positive.1
  have hd := r.g.lengths_positive.2.1
  have hc := r.g.lengths_positive.2.2.1
  have hvc : r.g.v < r.g.c := lt_trans r.v_lt (sub_pos.mp hp.2.2.1)
  have htc : r.t < r.g.c := sub_pos.mp hp.2.2.1
  have hq0 := r.weight_nonnegative 0
  have hq1 := r.weight_nonnegative 1
  have hq2 := r.weight_nonnegative 2
  have hα := le_of_lt r.alpha_bounds.1
  have h1α := sub_nonneg.mpr (le_of_lt r.alpha_bounds.2)
  let d0 : ℝ := r.weight 0 / (r.g.c - r.g.v)
  let d1 : ℝ := r.weight 1 / (r.t - r.g.v)
  let d2 : ℝ := r.weight 2 / (r.g.c - r.t)
  let e0 : ℝ := (1 - r.alpha) / (r.g.c - r.g.v)
  let e1 : ℝ := r.alpha / (r.t - r.g.v)
  have hd0 : 0 ≤ d0 := div_nonneg hq0 (le_of_lt (sub_pos.mpr hvc))
  have hd1 : 0 ≤ d1 := div_nonneg hq1 (le_of_lt (sub_pos.mpr r.v_lt))
  have hd2 : 0 ≤ d2 := div_nonneg hq2 (le_of_lt hp.2.2.1)
  have he0 : 0 ≤ e0 := div_nonneg h1α (le_of_lt (sub_pos.mpr hvc))
  have he1 : 0 ≤ e1 := div_nonneg hα (le_of_lt (sub_pos.mpr r.v_lt))
  have hl : d0 + d1 = e0 + e1 := by
    dsimp [d0, d1, e0, e1, weight, alpha]
    field_simp [ne_of_gt hp.2.2.2.2, ne_of_gt hp.2.2.1,
      ne_of_gt (sub_pos.mpr hvc), ne_of_gt (sub_pos.mpr r.v_lt)]
    dsimp [K, s, ThreeGeometry.c, ThreeGeometry.d, ThreeGeometry.G]
    ring
  have hh : d0 + d2 = e0 := by
    dsimp [d0, d2, e0, weight, alpha]
    field_simp [ne_of_gt hp.2.2.2.2, ne_of_gt hp.2.2.1, ne_of_gt (sub_pos.mpr hvc)]
    dsimp [K, s, ThreeGeometry.c, ThreeGeometry.d, ThreeGeometry.G]
    ring
  have hs : rawInterval r.g.v r.g.c = rawInterval r.g.v r.t + rawInterval r.t r.g.c :=
    (rawInterval_glue (le_of_lt r.v_lt) (le_of_lt htc)).symm
  rw [r.law_marginal]
  simp [vertex, edges, Fin.sum_univ_succ]
  rw [affineUniform_scaled_interval hvc hq0, affineUniform_scaled_interval r.v_lt hq1,
    affineUniform_scaled_interval_reverse htc hq2]
  change ENNReal.ofReal d0 • rawInterval r.g.v r.g.c +
    (ENNReal.ofReal d1 • rawInterval r.g.v r.t + ENNReal.ofReal d2 • rawInterval r.t r.g.c) = _
  calc
    _ = ENNReal.ofReal (d0 + d1) • rawInterval r.g.v r.t +
        ENNReal.ofReal (d0 + d2) • rawInterval r.t r.g.c := by
      rw [hs, smul_add, ofReal_smul_add hd0 hd1, ofReal_smul_add hd0 hd2]
      simp only [add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal (e0 + e1) • rawInterval r.g.v r.t +
        ENNReal.ofReal e0 • rawInterval r.t r.g.c := by rw [hl, hh]
    _ = ENNReal.ofReal e1 • rawInterval r.g.v r.t +
        ENNReal.ofReal e0 • rawInterval r.g.v r.g.c := by
      rw [hs, smul_add, ofReal_smul_add he0 he1]
      simp only [add_assoc, add_comm]
    _ = r.targetLaw := by
      rw [targetLaw, affineUniform_scaled_interval r.v_lt hα, affineUniform_scaled_interval hvc h1α]

/-- The residual sampler remains feasible on every retained or zero-weight edge,
for every interpolation parameter in the unit interval. -/
theorem pointwise_fullBudget (r : NestedResidual) (i : Fin 3) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget r.g.budget (segmentPoint (r.vertex (edges i).1) (r.vertex (edges i).2) t) :=
  segment_fullBudget (r.vertex_fullBudget _) (r.vertex_fullBudget _) ht

/-- A closed whole-law contract for the middle case's residual component. -/
theorem coupling_contract (r : NestedResidual) :
    (∀ᵐ x ∂(r.law : Measure (Allocation 3)), FullBudget r.g.budget x) ∧
    (marginal r.law 0 : Measure ℝ) = uniformLaw r.g.a ∧
    (marginal r.law 1 : Measure ℝ) = uniformLaw r.g.d ∧
    (marginal r.law 2 : Measure ℝ) = r.targetLaw :=
  ⟨r.law_fullBudget, r.law_marginal_x, r.law_marginal_y, r.law_marginal_z⟩

end NestedResidual

namespace NestedInput

noncomputable def residualInput (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    NestedResidual where
  g := i.geometry
  t := i.t
  h_pos := i.h_pos
  v_lt := hvt
  lt_u := htu

/-- The residual component uses the original input's first two uniform lengths
and budget; its third measure is precisely the translated nested mixture. -/
theorem residual_coupling (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    ∃ μ : Mixed 3, (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget i.M x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal μ 2 : Measure ℝ) = (i.residualInput hvt htu).targetLaw := by
  have he := i.geometry_matches
  refine ⟨(i.residualInput hvt htu).law, ?_⟩
  simpa only [residualInput, he.1, he.2.1, he.2.2.2] using
    (i.residualInput hvt htu).coupling_contract

end NestedInput
end Blotto
