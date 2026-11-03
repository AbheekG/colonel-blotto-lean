import Blotto.ThreeMixture

/-! Measure-level coordinate laws of the three-variable segment construction.
Interval pieces may have zero length; every scalar identity uses only the
strictly positive global lengths a,c,d,E,F as denominators. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

theorem uniformLaw_density {a : ℝ} (ha : 0 < a) :
    uniformLaw a = ENNReal.ofReal (1 / a) • rawInterval 0 a := by
  rw [one_div, ENNReal.ofReal_inv_of_pos ha]
  rfl

theorem ofReal_smul_add {α : Type*} [MeasurableSpace α] {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (μ : Measure α) :
    ENNReal.ofReal (r + s) • μ = ENNReal.ofReal r • μ + ENNReal.ofReal s • μ := by
  rw [ENNReal.ofReal_add hr hs, add_smul]

namespace ThreeGeometry

theorem first_marginal_x (g : ThreeGeometry) (hwv : g.w ≤ g.v) :
    (marginal (g.tableLaw g.firstWeights (g.firstWeights_nonnegative hwv)
      g.firstWeights_mass) 0 : Measure ℝ) = uniformLaw g.a := by
  have ha := g.lengths_positive.1
  have hc := g.lengths_positive.2.2.1
  have hE := g.lengths_positive.2.2.2.1
  have hq := g.firstWeights_nonnegative hwv
  let r : ℝ := g.h / (g.c * g.E)
  let m : ℝ := g.firstWeights.q13 + g.firstWeights.q14 +
    g.firstWeights.q36 + g.firstWeights.q46
  have hr : 0 ≤ r := div_nonneg g.h_nonneg (le_of_lt (mul_pos hc hE))
  have hm : 0 ≤ m := by dsimp [m]; linarith [hq.1, hq.2.1, hq.2.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.2]
  have h26 : g.firstWeights.q26 = (g.w - 0) * r := by
    dsimp [firstWeights, r]; ring
  have h25 : g.firstWeights.q25 = (g.v - g.w) * r := by
    dsimp [firstWeights, r]; ring
  have h45 : g.firstWeights.q45 = (g.a - g.v) * r := by
    dsimp [firstWeights, r]
    field_simp [ne_of_gt hc, ne_of_gt hE]
    dsimp [a, E]; ring
  have htotal : m + g.a * r = 1 := by
    have he := g.first_x_density
    change m / g.a + r = 1 / g.a at he
    field_simp [ne_of_gt ha] at he
    nlinarith
  have hva : g.v ≤ g.a := by dsimp [a]; linarith [g.w_nonneg, g.h_nonneg]
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.firstWeights.q15 = 0 from rfl, show g.firstWeights.q24 = 0 from rfl,
    ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [affineUniform_reverse g.a 0, affineUniform_reverse g.w 0,
    affineUniform_reverse g.a g.v, h26, h25, h45,
    weighted_affine_interval g.w_nonneg hr, weighted_affine_interval hwv hr,
    weighted_affine_interval hva hr]
  calc
    _ = ENNReal.ofReal m • (affineUniform 0 g.a : Measure ℝ) +
        (ENNReal.ofReal r • rawInterval 0 g.w + ENNReal.ofReal r • rawInterval g.w g.v +
          ENNReal.ofReal r • rawInterval g.v g.a) := by
      dsimp [m]
      rw [ENNReal.ofReal_add (by linarith [hq.1, hq.2.1, hq.2.2.2.2.2.2.1]) hq.2.2.2.2.2.2.2.2,
        ENNReal.ofReal_add (by linarith [hq.1, hq.2.1]) hq.2.2.2.2.2.2.1,
        ENNReal.ofReal_add hq.1 hq.2.1]
      simp only [add_smul]
      simp only [add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal m • (affineUniform 0 g.a : Measure ℝ) +
        ENNReal.ofReal r • rawInterval 0 g.a := by
      rw [rawInterval_scaled_glue_three g.w_nonneg hwv hva]
    _ = ENNReal.ofReal (m + g.a * r) • (affineUniform 0 g.a : Measure ℝ) := by
      rw [ofReal_smul_add hm (mul_nonneg (le_of_lt ha) hr),
        show g.a * r = (g.a - 0) * r by ring, weighted_affine_interval (le_of_lt ha) hr]
    _ = uniformLaw g.a := by
      rw [htotal, ENNReal.ofReal_one, one_smul, affineUniform_increasing ha]
      simp only [intervalLaw, sub_zero, uniformLaw]

/-- The zero atom and continuous density of the mixed third-coordinate target. -/
theorem target_z_density (g : ThreeGeometry) :
    zeroUniformLaw g.c g.mixtureProbability =
      ENNReal.ofReal (g.h / g.c) • Measure.dirac 0 +
        ENNReal.ofReal (g.mixtureProbability / g.c) • rawInterval 0 g.c := by
  have hp := le_of_lt g.mixtureProbability_bounds.1
  rw [zeroUniformLaw, ← g.atom_weight, uniformLaw_density g.lengths_positive.2.2.1,
    smul_smul, ← ENNReal.ofReal_mul hp]
  congr 1
  congr 1
  congr 1
  ring

/-- Exact y-coordinate law of the first table, including collapsed pieces. -/
theorem first_marginal_y (g : ThreeGeometry) (hwv : g.w ≤ g.v) :
    (marginal (g.tableLaw g.firstWeights (g.firstWeights_nonnegative hwv)
      g.firstWeights_mass) 1 : Measure ℝ) = uniformLaw g.d := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  rcases g.lengths_positive with ⟨ha, hd, hc, hE, hF⟩
  have hq := g.firstWeights_nonnegative hwv
  rcases hq with ⟨hq13, hq14, hq15, hq24, hq25, hq26, hq36, hq45, hq46⟩
  have huw := sub_nonneg.mpr (le_trans hwv g.ordered)
  have hvw := sub_nonneg.mpr hwv
  have ho0 : 0 ≤ g.w := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho1 : g.w ≤ g.u := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho2 : g.u ≤ g.d := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  let r13 : ℝ := g.G * g.R / (g.a * g.c * g.E * g.F)
  have hr13 : 0 ≤ r13 := by dsimp [r13, G, R, S]; positivity
  have hm13 : g.firstWeights.q13 = (g.w - 0) * r13 := by
    dsimp [r13, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he13 : ENNReal.ofReal (g.firstWeights.q13) •
      (affineUniform g.w 0 : Measure ℝ) =
        ENNReal.ofReal r13 • rawInterval 0 g.w := by
    rw [hm13]
    apply weighted_affine_interval_reverse (by linarith) hr13
  let r14 : ℝ := g.G * g.R / (g.a * g.c * g.E * g.F)
  have hr14 : 0 ≤ r14 := by dsimp [r14, G, R, S]; positivity
  have hm14 : g.firstWeights.q14 = (g.u - g.w) * r14 := by
    dsimp [r14, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF]

  have he14 : ENNReal.ofReal (g.firstWeights.q14) •
      (affineUniform g.w g.u : Measure ℝ) =
        ENNReal.ofReal r14 • rawInterval g.w g.u := by
    rw [hm14]
    apply weighted_affine_interval (by linarith) hr14
  let r25 : ℝ := g.firstWeights.q25 / g.d
  have hr25 : 0 ≤ r25 := by dsimp [r25, G, R, S]; positivity
  have hm25 : g.firstWeights.q25 = (g.d - 0) * r25 := by
    dsimp [r25, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he25 : ENNReal.ofReal (g.firstWeights.q25) •
      (affineUniform 0 g.d : Measure ℝ) =
        ENNReal.ofReal r25 • rawInterval 0 g.d := by
    rw [hm25]
    apply weighted_affine_interval (by linarith) hr25
  let r26 : ℝ := g.firstWeights.q26 / g.d
  have hr26 : 0 ≤ r26 := by dsimp [r26, G, R, S]; positivity
  have hm26 : g.firstWeights.q26 = (g.d - 0) * r26 := by
    dsimp [r26, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he26 : ENNReal.ofReal (g.firstWeights.q26) •
      (affineUniform 0 g.d : Measure ℝ) =
        ENNReal.ofReal r26 • rawInterval 0 g.d := by
    rw [hm26]
    apply weighted_affine_interval (by linarith) hr26
  let r36 : ℝ := g.firstWeights.q36 / g.d
  have hr36 : 0 ≤ r36 := by dsimp [r36, G, R, S]; positivity
  have hm36 : g.firstWeights.q36 = (g.d - 0) * r36 := by
    dsimp [r36, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he36 : ENNReal.ofReal (g.firstWeights.q36) •
      (affineUniform 0 g.d : Measure ℝ) =
        ENNReal.ofReal r36 • rawInterval 0 g.d := by
    rw [hm36]
    apply weighted_affine_interval (by linarith) hr36
  let r45 : ℝ := g.h / (g.c * g.E)
  have hr45 : 0 ≤ r45 := by dsimp [r45, G, R, S]; positivity
  have hm45 : g.firstWeights.q45 = (g.d - g.u) * r45 := by
    dsimp [r45, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he45 : ENNReal.ofReal (g.firstWeights.q45) •
      (affineUniform g.u g.d : Measure ℝ) =
        ENNReal.ofReal r45 • rawInterval g.u g.d := by
    rw [hm45]
    apply weighted_affine_interval (by linarith) hr45
  let r46 : ℝ := g.firstWeights.q46 / g.E
  have hr46 : 0 ≤ r46 := by dsimp [r46, G, R, S]; positivity
  have hm46 : g.firstWeights.q46 = (g.d - g.u) * r46 := by
    dsimp [r46, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he46 : ENNReal.ofReal (g.firstWeights.q46) •
      (affineUniform g.u g.d : Measure ℝ) =
        ENNReal.ofReal r46 • rawInterval g.u g.d := by
    rw [hm46]
    apply weighted_affine_interval (by linarith) hr46
  have hc0 : r13 + r25 + r26 + r36 = 1 / g.d := by
    dsimp [r13, r25, r26, r36, firstWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec0 : ENNReal.ofReal r13 + ENNReal.ofReal r25 + ENNReal.ofReal r26 + ENNReal.ofReal r36 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr13 hr25, ← ENNReal.ofReal_add (add_nonneg hr13 hr25) hr26, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr13 hr25) hr26) hr36]
    rw [hc0]
  have hc1 : r14 + r25 + r26 + r36 = 1 / g.d := by
    dsimp [r14, r25, r26, r36, firstWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec1 : ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r26 + ENNReal.ofReal r36 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr14 hr25, ← ENNReal.ofReal_add (add_nonneg hr14 hr25) hr26, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr14 hr25) hr26) hr36]
    rw [hc1]
  have hc2 : r25 + r26 + r36 + r45 + r46 = 1 / g.d := by
    dsimp [r25, r26, r36, r45, r46, firstWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec2 : ENNReal.ofReal r25 + ENNReal.ofReal r26 + ENNReal.ofReal r36 + ENNReal.ofReal r45 + ENNReal.ofReal r46 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr25 hr26, ← ENNReal.ofReal_add (add_nonneg hr25 hr26) hr36, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr25 hr26) hr36) hr45, ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg hr25 hr26) hr36) hr45) hr46]
    rw [hc2]
  have hs03 : rawInterval 0 g.d = rawInterval 0 g.w + rawInterval g.w g.u + rawInterval g.u g.d :=
    (rawInterval_glue_three ho0 ho1 ho2).symm
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.firstWeights.q15 = 0 from rfl, show g.firstWeights.q24 = 0 from rfl, ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [he13, he14, he25, he26, he36, he45, he46]
  calc
    _ = (ENNReal.ofReal r13 + ENNReal.ofReal r25 + ENNReal.ofReal r26 + ENNReal.ofReal r36) • rawInterval 0 g.w + (ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r26 + ENNReal.ofReal r36) • rawInterval g.w g.u + (ENNReal.ofReal r25 + ENNReal.ofReal r26 + ENNReal.ofReal r36 + ENNReal.ofReal r45 + ENNReal.ofReal r46) • rawInterval g.u g.d := by
      simp only [hs03,smul_add,add_smul]
      generalize ENNReal.ofReal r13 = s13
      generalize ENNReal.ofReal r25 = s25
      generalize ENNReal.ofReal r26 = s26
      generalize ENNReal.ofReal r36 = s36
      generalize ENNReal.ofReal r14 = s14
      generalize ENNReal.ofReal r45 = s45
      generalize ENNReal.ofReal r46 = s46
      generalize rawInterval 0 g.w = μ0
      generalize rawInterval g.w g.u = μ1
      generalize rawInterval g.u g.d = μ2
      simp only [add_assoc, add_left_comm]
    _ = ENNReal.ofReal (1 / g.d) • rawInterval 0 g.d := by
      try rw [hec0]
      try rw [hec1]
      try rw [hec2]
      rw [rawInterval_scaled_glue_three ho0 ho1 ho2]
    _ = _ := by
      exact (uniformLaw_density hd).symm

/-- Exact z-coordinate law of the first table, including collapsed pieces. -/
theorem first_marginal_z (g : ThreeGeometry) (hwv : g.w ≤ g.v) :
    (marginal (g.tableLaw g.firstWeights (g.firstWeights_nonnegative hwv)
      g.firstWeights_mass) 2 : Measure ℝ) = zeroUniformLaw g.c g.mixtureProbability := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  rcases g.lengths_positive with ⟨ha, hd, hc, hE, hF⟩
  have hq := g.firstWeights_nonnegative hwv
  rcases hq with ⟨hq13, hq14, hq15, hq24, hq25, hq26, hq36, hq45, hq46⟩
  have huw := sub_nonneg.mpr (le_trans hwv g.ordered)
  have hvw := sub_nonneg.mpr hwv
  have ho0 : 0 ≤ g.v := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho1 : g.v ≤ g.u := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho2 : g.u ≤ g.c := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  let r13 : ℝ := g.w * g.R / (g.a * g.c * g.E * g.F)
  have hr13 : 0 ≤ r13 := by dsimp [r13, G, R, S]; positivity
  have hm13 : g.firstWeights.q13 = (g.c - g.u) * r13 := by
    dsimp [r13, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he13 : ENNReal.ofReal (g.firstWeights.q13) •
      (affineUniform g.c g.u : Measure ℝ) =
        ENNReal.ofReal r13 • rawInterval g.u g.c := by
    rw [hm13]
    apply weighted_affine_interval_reverse (by linarith) hr13
  let r14 : ℝ := g.firstWeights.q14 / g.c
  have hr14 : 0 ≤ r14 := by dsimp [r14, G, R, S]; positivity
  have hm14 : g.firstWeights.q14 = (g.c - 0) * r14 := by
    dsimp [r14, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he14 : ENNReal.ofReal (g.firstWeights.q14) •
      (affineUniform g.c 0 : Measure ℝ) =
        ENNReal.ofReal r14 • rawInterval 0 g.c := by
    rw [hm14]
    apply weighted_affine_interval_reverse (by linarith) hr14
  let r25 : ℝ := g.firstWeights.q25 / g.c
  have hr25 : 0 ≤ r25 := by dsimp [r25, G, R, S]; positivity
  have hm25 : g.firstWeights.q25 = (g.c - 0) * r25 := by
    dsimp [r25, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he25 : ENNReal.ofReal (g.firstWeights.q25) •
      (affineUniform g.c 0 : Measure ℝ) =
        ENNReal.ofReal r25 • rawInterval 0 g.c := by
    rw [hm25]
    apply weighted_affine_interval_reverse (by linarith) hr25
  let r26 : ℝ := g.w * g.h / (g.c * g.E * g.F)
  have hr26 : 0 ≤ r26 := by dsimp [r26, G, R, S]; positivity
  have hm26 : g.firstWeights.q26 = (g.c - g.v) * r26 := by
    dsimp [r26, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he26 : ENNReal.ofReal (g.firstWeights.q26) •
      (affineUniform g.c g.v : Measure ℝ) =
        ENNReal.ofReal r26 • rawInterval g.v g.c := by
    rw [hm26]
    apply weighted_affine_interval_reverse (by linarith) hr26
  let r36 : ℝ := g.w * g.R / (g.a * g.c * g.E * g.F)
  have hr36 : 0 ≤ r36 := by dsimp [r36, G, R, S]; positivity
  have hm36 : g.firstWeights.q36 = (g.u - g.v) * r36 := by
    dsimp [r36, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF]

  have he36 : ENNReal.ofReal (g.firstWeights.q36) •
      (affineUniform g.u g.v : Measure ℝ) =
        ENNReal.ofReal r36 • rawInterval g.v g.u := by
    rw [hm36]
    apply weighted_affine_interval_reverse (by linarith) hr36
  let r46 : ℝ := g.w * (g.u + g.v + 2 * g.h) / (g.a * g.c * g.F)
  have hr46 : 0 ≤ r46 := by dsimp [r46, G, R, S]; positivity
  have hm46 : g.firstWeights.q46 = (g.v - 0) * r46 := by
    dsimp [r46, firstWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      ring
  have he46 : ENNReal.ofReal (g.firstWeights.q46) •
      (affineUniform 0 g.v : Measure ℝ) =
        ENNReal.ofReal r46 • rawInterval 0 g.v := by
    rw [hm46]
    apply weighted_affine_interval (by linarith) hr46
  have hc0 : r14 + r25 + r46 = g.mixtureProbability / g.c := by
    dsimp [r14, r25, r46, firstWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec0 : ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r46 = ENNReal.ofReal (g.mixtureProbability / g.c) := by
    rw [← ENNReal.ofReal_add hr14 hr25, ← ENNReal.ofReal_add (add_nonneg hr14 hr25) hr46]
    rw [hc0]
  have hc1 : r14 + r25 + r26 + r36 = g.mixtureProbability / g.c := by
    dsimp [r14, r25, r26, r36, firstWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec1 : ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r26 + ENNReal.ofReal r36 = ENNReal.ofReal (g.mixtureProbability / g.c) := by
    rw [← ENNReal.ofReal_add hr14 hr25, ← ENNReal.ofReal_add (add_nonneg hr14 hr25) hr26, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr14 hr25) hr26) hr36]
    rw [hc1]
  have hc2 : r13 + r14 + r25 + r26 = g.mixtureProbability / g.c := by
    dsimp [r13, r14, r25, r26, firstWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec2 : ENNReal.ofReal r13 + ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r26 = ENNReal.ofReal (g.mixtureProbability / g.c) := by
    rw [← ENNReal.ofReal_add hr13 hr14, ← ENNReal.ofReal_add (add_nonneg hr13 hr14) hr25, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr13 hr14) hr25) hr26]
    rw [hc2]
  have hs03 : rawInterval 0 g.c = rawInterval 0 g.v + rawInterval g.v g.u + rawInterval g.u g.c :=
    (rawInterval_glue_three ho0 ho1 ho2).symm
  have hs13 : rawInterval g.v g.c = rawInterval g.v g.u + rawInterval g.u g.c :=
    (rawInterval_glue ho1 ho2).symm
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.firstWeights.q15 = 0 from rfl, show g.firstWeights.q24 = 0 from rfl, ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [he13, he14, he25, he26, he36, he46, affineUniform_constant]
  calc
    _ = ENNReal.ofReal (g.firstWeights.q45) • Measure.dirac 0 + (ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r46) • rawInterval 0 g.v + (ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r26 + ENNReal.ofReal r36) • rawInterval g.v g.u + (ENNReal.ofReal r13 + ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r26) • rawInterval g.u g.c := by
      simp only [hs03,hs13,smul_add,add_smul]
      generalize ENNReal.ofReal r14 = s14
      generalize ENNReal.ofReal r25 = s25
      generalize ENNReal.ofReal r46 = s46
      generalize ENNReal.ofReal r26 = s26
      generalize ENNReal.ofReal r36 = s36
      generalize ENNReal.ofReal r13 = s13
      generalize rawInterval 0 g.v = μ0
      generalize rawInterval g.v g.u = μ1
      generalize rawInterval g.u g.c = μ2
      simp only [add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal (g.firstWeights.q45) • Measure.dirac 0 + ENNReal.ofReal (g.mixtureProbability / g.c) • rawInterval 0 g.c := by
      try rw [hec0]
      try rw [hec1]
      try rw [hec2]
      simpa only [add_assoc] using
        congrArg (fun μ : Measure ℝ => ENNReal.ofReal (g.firstWeights.q45) • Measure.dirac 0 + μ)
          (rawInterval_scaled_glue_three (r := g.mixtureProbability / g.c) ho0 ho1 ho2)
    _ = _ := by
      exact g.target_z_density.symm

/-- Exact x-coordinate law of the second table, including collapsed pieces. -/
theorem second_marginal_x (g : ThreeGeometry) (hwu : g.w ≤ g.u) :
    (marginal (g.tableLaw g.secondWeights (g.secondWeights_nonnegative hwu)
      g.secondWeights_mass) 0 : Measure ℝ) = uniformLaw g.a := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  rcases g.lengths_positive with ⟨ha, hd, hc, hE, hF⟩
  have hq := g.secondWeights_nonnegative hwu
  rcases hq with ⟨hq13, hq14, hq15, hq24, hq25, hq26, hq36, hq45, hq46⟩
  have huw := sub_nonneg.mpr hwu
  have ho0 : 0 ≤ g.v := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho1 : g.v ≤ g.a := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  let r13 : ℝ := g.secondWeights.q13 / g.a
  have hr13 : 0 ≤ r13 := by dsimp [r13, G, R, S]; positivity
  have hm13 : g.secondWeights.q13 = (g.a - 0) * r13 := by
    dsimp [r13, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he13 : ENNReal.ofReal (g.secondWeights.q13) •
      (affineUniform 0 g.a : Measure ℝ) =
        ENNReal.ofReal r13 • rawInterval 0 g.a := by
    rw [hm13]
    apply weighted_affine_interval (by linarith) hr13
  let r14 : ℝ := g.secondWeights.q14 / g.a
  have hr14 : 0 ≤ r14 := by dsimp [r14, G, R, S]; positivity
  have hm14 : g.secondWeights.q14 = (g.a - 0) * r14 := by
    dsimp [r14, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he14 : ENNReal.ofReal (g.secondWeights.q14) •
      (affineUniform 0 g.a : Measure ℝ) =
        ENNReal.ofReal r14 • rawInterval 0 g.a := by
    rw [hm14]
    apply weighted_affine_interval (by linarith) hr14
  let r15 : ℝ := g.h / (g.c * g.E)
  have hr15 : 0 ≤ r15 := by dsimp [r15, G, R, S]; positivity
  have hm15 : g.secondWeights.q15 = (g.v - 0) * r15 := by
    dsimp [r15, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      ring
  have he15 : ENNReal.ofReal (g.secondWeights.q15) •
      (affineUniform 0 g.v : Measure ℝ) =
        ENNReal.ofReal r15 • rawInterval 0 g.v := by
    rw [hm15]
    apply weighted_affine_interval (by linarith) hr15
  let r36 : ℝ := g.secondWeights.q36 / g.a
  have hr36 : 0 ≤ r36 := by dsimp [r36, G, R, S]; positivity
  have hm36 : g.secondWeights.q36 = (g.a - 0) * r36 := by
    dsimp [r36, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he36 : ENNReal.ofReal (g.secondWeights.q36) •
      (affineUniform g.a 0 : Measure ℝ) =
        ENNReal.ofReal r36 • rawInterval 0 g.a := by
    rw [hm36]
    apply weighted_affine_interval_reverse (by linarith) hr36
  let r45 : ℝ := g.h / (g.c * g.E)
  have hr45 : 0 ≤ r45 := by dsimp [r45, G, R, S]; positivity
  have hm45 : g.secondWeights.q45 = (g.a - g.v) * r45 := by
    dsimp [r45, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he45 : ENNReal.ofReal (g.secondWeights.q45) •
      (affineUniform g.a g.v : Measure ℝ) =
        ENNReal.ofReal r45 • rawInterval g.v g.a := by
    rw [hm45]
    apply weighted_affine_interval_reverse (by linarith) hr45
  let r46 : ℝ := g.secondWeights.q46 / g.a
  have hr46 : 0 ≤ r46 := by dsimp [r46, G, R, S]; positivity
  have hm46 : g.secondWeights.q46 = (g.a - 0) * r46 := by
    dsimp [r46, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he46 : ENNReal.ofReal (g.secondWeights.q46) •
      (affineUniform g.a 0 : Measure ℝ) =
        ENNReal.ofReal r46 • rawInterval 0 g.a := by
    rw [hm46]
    apply weighted_affine_interval_reverse (by linarith) hr46
  have hc0 : r13 + r14 + r15 + r36 + r46 = 1 / g.a := by
    dsimp [r13, r14, r15, r36, r46, secondWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec0 : ENNReal.ofReal r13 + ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r36 + ENNReal.ofReal r46 = ENNReal.ofReal (1 / g.a) := by
    rw [← ENNReal.ofReal_add hr13 hr14, ← ENNReal.ofReal_add (add_nonneg hr13 hr14) hr15, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr13 hr14) hr15) hr36, ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg hr13 hr14) hr15) hr36) hr46]
    rw [hc0]
  have hc1 : r13 + r14 + r36 + r45 + r46 = 1 / g.a := by
    dsimp [r13, r14, r36, r45, r46, secondWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec1 : ENNReal.ofReal r13 + ENNReal.ofReal r14 + ENNReal.ofReal r36 + ENNReal.ofReal r45 + ENNReal.ofReal r46 = ENNReal.ofReal (1 / g.a) := by
    rw [← ENNReal.ofReal_add hr13 hr14, ← ENNReal.ofReal_add (add_nonneg hr13 hr14) hr36, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr13 hr14) hr36) hr45, ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg hr13 hr14) hr36) hr45) hr46]
    rw [hc1]
  have hs02 : rawInterval 0 g.a = rawInterval 0 g.v + rawInterval g.v g.a :=
    (rawInterval_glue ho0 ho1).symm
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.secondWeights.q24 = 0 from rfl, show g.secondWeights.q25 = 0 from rfl, show g.secondWeights.q26 = 0 from rfl, ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [he13, he14, he15, he36, he45, he46]
  calc
    _ = (ENNReal.ofReal r13 + ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r36 + ENNReal.ofReal r46) • rawInterval 0 g.v + (ENNReal.ofReal r13 + ENNReal.ofReal r14 + ENNReal.ofReal r36 + ENNReal.ofReal r45 + ENNReal.ofReal r46) • rawInterval g.v g.a := by
      simp only [hs02,smul_add,add_smul]
      generalize ENNReal.ofReal r13 = s13
      generalize ENNReal.ofReal r14 = s14
      generalize ENNReal.ofReal r15 = s15
      generalize ENNReal.ofReal r36 = s36
      generalize ENNReal.ofReal r46 = s46
      generalize ENNReal.ofReal r45 = s45
      generalize rawInterval 0 g.v = μ0
      generalize rawInterval g.v g.a = μ1
      simp only [add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal (1 / g.a) • rawInterval 0 g.a := by
      try rw [hec0]
      try rw [hec1]
      rw [rawInterval_scaled_glue ho0 ho1]
    _ = _ := by
      exact (uniformLaw_density ha).symm

/-- Exact y-coordinate law of the second table, including collapsed pieces. -/
theorem second_marginal_y (g : ThreeGeometry) (hwu : g.w ≤ g.u) :
    (marginal (g.tableLaw g.secondWeights (g.secondWeights_nonnegative hwu)
      g.secondWeights_mass) 1 : Measure ℝ) = uniformLaw g.d := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  rcases g.lengths_positive with ⟨ha, hd, hc, hE, hF⟩
  have hq := g.secondWeights_nonnegative hwu
  rcases hq with ⟨hq13, hq14, hq15, hq24, hq25, hq26, hq36, hq45, hq46⟩
  have huw := sub_nonneg.mpr hwu
  have ho0 : 0 ≤ g.w := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho1 : g.w ≤ g.u := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho2 : g.u ≤ g.d := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  let r13 : ℝ := g.G / (g.a * g.F)
  have hr13 : 0 ≤ r13 := by dsimp [r13, G, R, S]; positivity
  have hm13 : g.secondWeights.q13 = (g.w - 0) * r13 := by
    dsimp [r13, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he13 : ENNReal.ofReal (g.secondWeights.q13) •
      (affineUniform g.w 0 : Measure ℝ) =
        ENNReal.ofReal r13 • rawInterval 0 g.w := by
    rw [hm13]
    apply weighted_affine_interval_reverse (by linarith) hr13
  let r14 : ℝ := g.S / (g.a * g.c * g.E * g.F)
  have hr14 : 0 ≤ r14 := by dsimp [r14, G, R, S]; positivity
  have hm14 : g.secondWeights.q14 = (g.u - g.w) * r14 := by
    dsimp [r14, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF]

  have he14 : ENNReal.ofReal (g.secondWeights.q14) •
      (affineUniform g.w g.u : Measure ℝ) =
        ENNReal.ofReal r14 • rawInterval g.w g.u := by
    rw [hm14]
    apply weighted_affine_interval (by linarith) hr14
  let r15 : ℝ := g.v * g.h / (g.c * g.E * g.F)
  have hr15 : 0 ≤ r15 := by dsimp [r15, G, R, S]; positivity
  have hm15 : g.secondWeights.q15 = (g.d - g.w) * r15 := by
    dsimp [r15, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he15 : ENNReal.ofReal (g.secondWeights.q15) •
      (affineUniform g.w g.d : Measure ℝ) =
        ENNReal.ofReal r15 • rawInterval g.w g.d := by
    rw [hm15]
    apply weighted_affine_interval (by linarith) hr15
  let r36 : ℝ := g.secondWeights.q36 / g.d
  have hr36 : 0 ≤ r36 := by dsimp [r36, G, R, S]; positivity
  have hm36 : g.secondWeights.q36 = (g.d - 0) * r36 := by
    dsimp [r36, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he36 : ENNReal.ofReal (g.secondWeights.q36) •
      (affineUniform 0 g.d : Measure ℝ) =
        ENNReal.ofReal r36 • rawInterval 0 g.d := by
    rw [hm36]
    apply weighted_affine_interval (by linarith) hr36
  let r45 : ℝ := g.h / (g.c * g.E)
  have hr45 : 0 ≤ r45 := by dsimp [r45, G, R, S]; positivity
  have hm45 : g.secondWeights.q45 = (g.d - g.u) * r45 := by
    dsimp [r45, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he45 : ENNReal.ofReal (g.secondWeights.q45) •
      (affineUniform g.u g.d : Measure ℝ) =
        ENNReal.ofReal r45 • rawInterval g.u g.d := by
    rw [hm45]
    apply weighted_affine_interval (by linarith) hr45
  let r46 : ℝ := g.secondWeights.q46 / g.E
  have hr46 : 0 ≤ r46 := by dsimp [r46, G, R, S]; positivity
  have hm46 : g.secondWeights.q46 = (g.d - g.u) * r46 := by
    dsimp [r46, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he46 : ENNReal.ofReal (g.secondWeights.q46) •
      (affineUniform g.u g.d : Measure ℝ) =
        ENNReal.ofReal r46 • rawInterval g.u g.d := by
    rw [hm46]
    apply weighted_affine_interval (by linarith) hr46
  have hc0 : r13 + r36 = 1 / g.d := by
    dsimp [r13, r36, secondWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec0 : ENNReal.ofReal r13 + ENNReal.ofReal r36 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr13 hr36]
    rw [hc0]
  have hc1 : r14 + r15 + r36 = 1 / g.d := by
    dsimp [r14, r15, r36, secondWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec1 : ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r36 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr14 hr15, ← ENNReal.ofReal_add (add_nonneg hr14 hr15) hr36]
    rw [hc1]
  have hc2 : r15 + r36 + r45 + r46 = 1 / g.d := by
    dsimp [r15, r36, r45, r46, secondWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec2 : ENNReal.ofReal r15 + ENNReal.ofReal r36 + ENNReal.ofReal r45 + ENNReal.ofReal r46 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr15 hr36, ← ENNReal.ofReal_add (add_nonneg hr15 hr36) hr45, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr15 hr36) hr45) hr46]
    rw [hc2]
  have hs03 : rawInterval 0 g.d = rawInterval 0 g.w + rawInterval g.w g.u + rawInterval g.u g.d :=
    (rawInterval_glue_three ho0 ho1 ho2).symm
  have hs13 : rawInterval g.w g.d = rawInterval g.w g.u + rawInterval g.u g.d :=
    (rawInterval_glue ho1 ho2).symm
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.secondWeights.q24 = 0 from rfl, show g.secondWeights.q25 = 0 from rfl, show g.secondWeights.q26 = 0 from rfl, ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [he13, he14, he15, he36, he45, he46]
  calc
    _ = (ENNReal.ofReal r13 + ENNReal.ofReal r36) • rawInterval 0 g.w + (ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r36) • rawInterval g.w g.u + (ENNReal.ofReal r15 + ENNReal.ofReal r36 + ENNReal.ofReal r45 + ENNReal.ofReal r46) • rawInterval g.u g.d := by
      simp only [hs03,hs13,smul_add,add_smul]
      generalize ENNReal.ofReal r13 = s13
      generalize ENNReal.ofReal r36 = s36
      generalize ENNReal.ofReal r14 = s14
      generalize ENNReal.ofReal r15 = s15
      generalize ENNReal.ofReal r45 = s45
      generalize ENNReal.ofReal r46 = s46
      generalize rawInterval 0 g.w = μ0
      generalize rawInterval g.w g.u = μ1
      generalize rawInterval g.u g.d = μ2
      simp only [add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal (1 / g.d) • rawInterval 0 g.d := by
      try rw [hec0]
      try rw [hec1]
      try rw [hec2]
      rw [rawInterval_scaled_glue_three ho0 ho1 ho2]
    _ = _ := by
      exact (uniformLaw_density hd).symm

/-- Exact z-coordinate law of the second table, including collapsed pieces. -/
theorem second_marginal_z (g : ThreeGeometry) (hwu : g.w ≤ g.u) :
    (marginal (g.tableLaw g.secondWeights (g.secondWeights_nonnegative hwu)
      g.secondWeights_mass) 2 : Measure ℝ) = zeroUniformLaw g.c g.mixtureProbability := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  rcases g.lengths_positive with ⟨ha, hd, hc, hE, hF⟩
  have hq := g.secondWeights_nonnegative hwu
  rcases hq with ⟨hq13, hq14, hq15, hq24, hq25, hq26, hq36, hq45, hq46⟩
  have huw := sub_nonneg.mpr hwu
  have ho0 : 0 ≤ g.v := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho1 : g.v ≤ g.u := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho2 : g.u ≤ g.c := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  let r13 : ℝ := g.w / (g.a * g.F)
  have hr13 : 0 ≤ r13 := by dsimp [r13, G, R, S]; positivity
  have hm13 : g.secondWeights.q13 = (g.c - g.u) * r13 := by
    dsimp [r13, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he13 : ENNReal.ofReal (g.secondWeights.q13) •
      (affineUniform g.c g.u : Measure ℝ) =
        ENNReal.ofReal r13 • rawInterval g.u g.c := by
    rw [hm13]
    apply weighted_affine_interval_reverse (by linarith) hr13
  let r14 : ℝ := g.secondWeights.q14 / g.c
  have hr14 : 0 ≤ r14 := by dsimp [r14, G, R, S]; positivity
  have hm14 : g.secondWeights.q14 = (g.c - 0) * r14 := by
    dsimp [r14, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he14 : ENNReal.ofReal (g.secondWeights.q14) •
      (affineUniform g.c 0 : Measure ℝ) =
        ENNReal.ofReal r14 • rawInterval 0 g.c := by
    rw [hm14]
    apply weighted_affine_interval_reverse (by linarith) hr14
  let r15 : ℝ := g.secondWeights.q15 / g.c
  have hr15 : 0 ≤ r15 := by dsimp [r15, G, R, S]; positivity
  have hm15 : g.secondWeights.q15 = (g.c - 0) * r15 := by
    dsimp [r15, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he15 : ENNReal.ofReal (g.secondWeights.q15) •
      (affineUniform g.c 0 : Measure ℝ) =
        ENNReal.ofReal r15 • rawInterval 0 g.c := by
    rw [hm15]
    apply weighted_affine_interval_reverse (by linarith) hr15
  let r36 : ℝ := g.w / (g.a * g.F)
  have hr36 : 0 ≤ r36 := by dsimp [r36, G, R, S]; positivity
  have hm36 : g.secondWeights.q36 = (g.u - g.v) * r36 := by
    dsimp [r36, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF]

  have he36 : ENNReal.ofReal (g.secondWeights.q36) •
      (affineUniform g.u g.v : Measure ℝ) =
        ENNReal.ofReal r36 • rawInterval g.v g.u := by
    rw [hm36]
    apply weighted_affine_interval_reverse (by linarith) hr36
  let r46 : ℝ := g.w / (g.a * g.F)
  have hr46 : 0 ≤ r46 := by dsimp [r46, G, R, S]; positivity
  have hm46 : g.secondWeights.q46 = (g.v - 0) * r46 := by
    dsimp [r46, secondWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      ring
  have he46 : ENNReal.ofReal (g.secondWeights.q46) •
      (affineUniform 0 g.v : Measure ℝ) =
        ENNReal.ofReal r46 • rawInterval 0 g.v := by
    rw [hm46]
    apply weighted_affine_interval (by linarith) hr46
  have hc0 : r14 + r15 + r46 = g.mixtureProbability / g.c := by
    dsimp [r14, r15, r46, secondWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec0 : ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r46 = ENNReal.ofReal (g.mixtureProbability / g.c) := by
    rw [← ENNReal.ofReal_add hr14 hr15, ← ENNReal.ofReal_add (add_nonneg hr14 hr15) hr46]
    rw [hc0]
  have hc1 : r14 + r15 + r36 = g.mixtureProbability / g.c := by
    dsimp [r14, r15, r36, secondWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec1 : ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r36 = ENNReal.ofReal (g.mixtureProbability / g.c) := by
    rw [← ENNReal.ofReal_add hr14 hr15, ← ENNReal.ofReal_add (add_nonneg hr14 hr15) hr36]
    rw [hc1]
  have hc2 : r13 + r14 + r15 = g.mixtureProbability / g.c := by
    dsimp [r13, r14, r15, secondWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec2 : ENNReal.ofReal r13 + ENNReal.ofReal r14 + ENNReal.ofReal r15 = ENNReal.ofReal (g.mixtureProbability / g.c) := by
    rw [← ENNReal.ofReal_add hr13 hr14, ← ENNReal.ofReal_add (add_nonneg hr13 hr14) hr15]
    rw [hc2]
  have hs03 : rawInterval 0 g.c = rawInterval 0 g.v + rawInterval g.v g.u + rawInterval g.u g.c :=
    (rawInterval_glue_three ho0 ho1 ho2).symm
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.secondWeights.q24 = 0 from rfl, show g.secondWeights.q25 = 0 from rfl, show g.secondWeights.q26 = 0 from rfl, ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [he13, he14, he15, he36, he46, affineUniform_constant]
  calc
    _ = ENNReal.ofReal (g.secondWeights.q45) • Measure.dirac 0 + (ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r46) • rawInterval 0 g.v + (ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r36) • rawInterval g.v g.u + (ENNReal.ofReal r13 + ENNReal.ofReal r14 + ENNReal.ofReal r15) • rawInterval g.u g.c := by
      simp only [hs03,smul_add,add_smul]
      generalize ENNReal.ofReal r14 = s14
      generalize ENNReal.ofReal r15 = s15
      generalize ENNReal.ofReal r46 = s46
      generalize ENNReal.ofReal r36 = s36
      generalize ENNReal.ofReal r13 = s13
      generalize rawInterval 0 g.v = μ0
      generalize rawInterval g.v g.u = μ1
      generalize rawInterval g.u g.c = μ2
      simp only [add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal (g.secondWeights.q45) • Measure.dirac 0 + ENNReal.ofReal (g.mixtureProbability / g.c) • rawInterval 0 g.c := by
      try rw [hec0]
      try rw [hec1]
      try rw [hec2]
      simpa only [add_assoc] using
        congrArg (fun μ : Measure ℝ => ENNReal.ofReal (g.secondWeights.q45) • Measure.dirac 0 + μ)
          (rawInterval_scaled_glue_three (r := g.mixtureProbability / g.c) ho0 ho1 ho2)
    _ = _ := by
      exact g.target_z_density.symm

/-- Exact x-coordinate law of the third table, including collapsed pieces. -/
theorem third_marginal_x (g : ThreeGeometry) (huw : g.u ≤ g.w) :
    (marginal (g.tableLaw g.thirdWeights (g.thirdWeights_nonnegative huw)
      g.thirdWeights_mass) 0 : Measure ℝ) = uniformLaw g.a := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  rcases g.lengths_positive with ⟨ha, hd, hc, hE, hF⟩
  have hq := g.thirdWeights_nonnegative huw
  rcases hq with ⟨hq13, hq14, hq15, hq24, hq25, hq26, hq36, hq45, hq46⟩
  have hwu := sub_nonneg.mpr huw
  have hwv := sub_nonneg.mpr (le_trans g.ordered huw)
  have ho0 : 0 ≤ g.v := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho1 : g.v ≤ g.w := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho2 : g.w ≤ g.a := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  let r14 : ℝ := g.thirdWeights.q14 / g.a
  have hr14 : 0 ≤ r14 := by dsimp [r14, G, R, S]; positivity
  have hm14 : g.thirdWeights.q14 = (g.a - 0) * r14 := by
    dsimp [r14, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he14 : ENNReal.ofReal (g.thirdWeights.q14) •
      (affineUniform 0 g.a : Measure ℝ) =
        ENNReal.ofReal r14 • rawInterval 0 g.a := by
    rw [hm14]
    apply weighted_affine_interval (by linarith) hr14
  let r15 : ℝ := g.F / (g.c * g.E)
  have hr15 : 0 ≤ r15 := by dsimp [r15, G, R, S]; positivity
  have hm15 : g.thirdWeights.q15 = (g.v - 0) * r15 := by
    dsimp [r15, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      ring
  have he15 : ENNReal.ofReal (g.thirdWeights.q15) •
      (affineUniform 0 g.v : Measure ℝ) =
        ENNReal.ofReal r15 • rawInterval 0 g.v := by
    rw [hm15]
    apply weighted_affine_interval (by linarith) hr15
  let r24 : ℝ := g.u / (g.c * g.E)
  have hr24 : 0 ≤ r24 := by dsimp [r24, G, R, S]; positivity
  have hm24 : g.thirdWeights.q24 = (g.a - g.w) * r24 := by
    dsimp [r24, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he24 : ENNReal.ofReal (g.thirdWeights.q24) •
      (affineUniform g.w g.a : Measure ℝ) =
        ENNReal.ofReal r24 • rawInterval g.w g.a := by
    rw [hm24]
    apply weighted_affine_interval (by linarith) hr24
  let r25 : ℝ := g.u / (g.c * g.E)
  have hr25 : 0 ≤ r25 := by dsimp [r25, G, R, S]; positivity
  have hm25 : g.thirdWeights.q25 = (g.w - g.v) * r25 := by
    dsimp [r25, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF]

  have he25 : ENNReal.ofReal (g.thirdWeights.q25) •
      (affineUniform g.w g.v : Measure ℝ) =
        ENNReal.ofReal r25 • rawInterval g.v g.w := by
    rw [hm25]
    apply weighted_affine_interval_reverse (by linarith) hr25
  let r45 : ℝ := g.h / (g.c * g.E)
  have hr45 : 0 ≤ r45 := by dsimp [r45, G, R, S]; positivity
  have hm45 : g.thirdWeights.q45 = (g.a - g.v) * r45 := by
    dsimp [r45, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he45 : ENNReal.ofReal (g.thirdWeights.q45) •
      (affineUniform g.a g.v : Measure ℝ) =
        ENNReal.ofReal r45 • rawInterval g.v g.a := by
    rw [hm45]
    apply weighted_affine_interval_reverse (by linarith) hr45
  have hc0 : r14 + r15 = 1 / g.a := by
    dsimp [r14, r15, thirdWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec0 : ENNReal.ofReal r14 + ENNReal.ofReal r15 = ENNReal.ofReal (1 / g.a) := by
    rw [← ENNReal.ofReal_add hr14 hr15]
    rw [hc0]
  have hc1 : r14 + r25 + r45 = 1 / g.a := by
    dsimp [r14, r25, r45, thirdWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec1 : ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r45 = ENNReal.ofReal (1 / g.a) := by
    rw [← ENNReal.ofReal_add hr14 hr25, ← ENNReal.ofReal_add (add_nonneg hr14 hr25) hr45]
    rw [hc1]
  have hc2 : r14 + r24 + r45 = 1 / g.a := by
    dsimp [r14, r24, r45, thirdWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec2 : ENNReal.ofReal r14 + ENNReal.ofReal r24 + ENNReal.ofReal r45 = ENNReal.ofReal (1 / g.a) := by
    rw [← ENNReal.ofReal_add hr14 hr24, ← ENNReal.ofReal_add (add_nonneg hr14 hr24) hr45]
    rw [hc2]
  have hs03 : rawInterval 0 g.a = rawInterval 0 g.v + rawInterval g.v g.w + rawInterval g.w g.a :=
    (rawInterval_glue_three ho0 ho1 ho2).symm
  have hs13 : rawInterval g.v g.a = rawInterval g.v g.w + rawInterval g.w g.a :=
    (rawInterval_glue ho1 ho2).symm
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.thirdWeights.q13 = 0 from rfl, show g.thirdWeights.q26 = 0 from rfl, show g.thirdWeights.q36 = 0 from rfl, show g.thirdWeights.q46 = 0 from rfl, ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [he14, he15, he24, he25, he45]
  calc
    _ = (ENNReal.ofReal r14 + ENNReal.ofReal r15) • rawInterval 0 g.v + (ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r45) • rawInterval g.v g.w + (ENNReal.ofReal r14 + ENNReal.ofReal r24 + ENNReal.ofReal r45) • rawInterval g.w g.a := by
      simp only [hs03,hs13,smul_add,add_smul]
      generalize ENNReal.ofReal r14 = s14
      generalize ENNReal.ofReal r15 = s15
      generalize ENNReal.ofReal r25 = s25
      generalize ENNReal.ofReal r45 = s45
      generalize ENNReal.ofReal r24 = s24
      generalize rawInterval 0 g.v = μ0
      generalize rawInterval g.v g.w = μ1
      generalize rawInterval g.w g.a = μ2
      simp only [add_zero, add_assoc, add_left_comm]
    _ = ENNReal.ofReal (1 / g.a) • rawInterval 0 g.a := by
      try rw [hec0]
      try rw [hec1]
      try rw [hec2]
      rw [rawInterval_scaled_glue_three ho0 ho1 ho2]
    _ = _ := by
      exact (uniformLaw_density ha).symm

/-- Exact y-coordinate law of the third table, including collapsed pieces. -/
theorem third_marginal_y (g : ThreeGeometry) (huw : g.u ≤ g.w) :
    (marginal (g.tableLaw g.thirdWeights (g.thirdWeights_nonnegative huw)
      g.thirdWeights_mass) 1 : Measure ℝ) = uniformLaw g.d := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  rcases g.lengths_positive with ⟨ha, hd, hc, hE, hF⟩
  have hq := g.thirdWeights_nonnegative huw
  rcases hq with ⟨hq13, hq14, hq15, hq24, hq25, hq26, hq36, hq45, hq46⟩
  have hwu := sub_nonneg.mpr huw
  have hwv := sub_nonneg.mpr (le_trans g.ordered huw)
  have ho0 : 0 ≤ g.u := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho1 : g.u ≤ g.w := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho2 : g.w ≤ g.d := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  let r14 : ℝ := g.v / (g.c * g.E)
  have hr14 : 0 ≤ r14 := by dsimp [r14, G, R, S]; positivity
  have hm14 : g.thirdWeights.q14 = (g.w - g.u) * r14 := by
    dsimp [r14, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF]

  have he14 : ENNReal.ofReal (g.thirdWeights.q14) •
      (affineUniform g.w g.u : Measure ℝ) =
        ENNReal.ofReal r14 • rawInterval g.u g.w := by
    rw [hm14]
    apply weighted_affine_interval_reverse (by linarith) hr14
  let r15 : ℝ := g.v / (g.c * g.E)
  have hr15 : 0 ≤ r15 := by dsimp [r15, G, R, S]; positivity
  have hm15 : g.thirdWeights.q15 = (g.d - g.w) * r15 := by
    dsimp [r15, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he15 : ENNReal.ofReal (g.thirdWeights.q15) •
      (affineUniform g.w g.d : Measure ℝ) =
        ENNReal.ofReal r15 • rawInterval g.w g.d := by
    rw [hm15]
    apply weighted_affine_interval (by linarith) hr15
  let r24 : ℝ := g.G / (g.c * g.E)
  have hr24 : 0 ≤ r24 := by dsimp [r24, G, R, S]; positivity
  have hm24 : g.thirdWeights.q24 = (g.u - 0) * r24 := by
    dsimp [r24, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he24 : ENNReal.ofReal (g.thirdWeights.q24) •
      (affineUniform 0 g.u : Measure ℝ) =
        ENNReal.ofReal r24 • rawInterval 0 g.u := by
    rw [hm24]
    apply weighted_affine_interval (by linarith) hr24
  let r25 : ℝ := g.thirdWeights.q25 / g.d
  have hr25 : 0 ≤ r25 := by dsimp [r25, G, R, S]; positivity
  have hm25 : g.thirdWeights.q25 = (g.d - 0) * r25 := by
    dsimp [r25, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he25 : ENNReal.ofReal (g.thirdWeights.q25) •
      (affineUniform 0 g.d : Measure ℝ) =
        ENNReal.ofReal r25 • rawInterval 0 g.d := by
    rw [hm25]
    apply weighted_affine_interval (by linarith) hr25
  let r45 : ℝ := g.h / (g.c * g.E)
  have hr45 : 0 ≤ r45 := by dsimp [r45, G, R, S]; positivity
  have hm45 : g.thirdWeights.q45 = (g.d - g.u) * r45 := by
    dsimp [r45, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he45 : ENNReal.ofReal (g.thirdWeights.q45) •
      (affineUniform g.u g.d : Measure ℝ) =
        ENNReal.ofReal r45 • rawInterval g.u g.d := by
    rw [hm45]
    apply weighted_affine_interval (by linarith) hr45
  have hc0 : r24 + r25 = 1 / g.d := by
    dsimp [r24, r25, thirdWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec0 : ENNReal.ofReal r24 + ENNReal.ofReal r25 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr24 hr25]
    rw [hc0]
  have hc1 : r14 + r25 + r45 = 1 / g.d := by
    dsimp [r14, r25, r45, thirdWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec1 : ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r45 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr14 hr25, ← ENNReal.ofReal_add (add_nonneg hr14 hr25) hr45]
    rw [hc1]
  have hc2 : r15 + r25 + r45 = 1 / g.d := by
    dsimp [r15, r25, r45, thirdWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec2 : ENNReal.ofReal r15 + ENNReal.ofReal r25 + ENNReal.ofReal r45 = ENNReal.ofReal (1 / g.d) := by
    rw [← ENNReal.ofReal_add hr15 hr25, ← ENNReal.ofReal_add (add_nonneg hr15 hr25) hr45]
    rw [hc2]
  have hs03 : rawInterval 0 g.d = rawInterval 0 g.u + rawInterval g.u g.w + rawInterval g.w g.d :=
    (rawInterval_glue_three ho0 ho1 ho2).symm
  have hs13 : rawInterval g.u g.d = rawInterval g.u g.w + rawInterval g.w g.d :=
    (rawInterval_glue ho1 ho2).symm
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.thirdWeights.q13 = 0 from rfl, show g.thirdWeights.q26 = 0 from rfl, show g.thirdWeights.q36 = 0 from rfl, show g.thirdWeights.q46 = 0 from rfl, ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [he14, he15, he24, he25, he45]
  calc
    _ = (ENNReal.ofReal r24 + ENNReal.ofReal r25) • rawInterval 0 g.u + (ENNReal.ofReal r14 + ENNReal.ofReal r25 + ENNReal.ofReal r45) • rawInterval g.u g.w + (ENNReal.ofReal r15 + ENNReal.ofReal r25 + ENNReal.ofReal r45) • rawInterval g.w g.d := by
      simp only [hs03,hs13,smul_add,add_smul]
      generalize ENNReal.ofReal r24 = s24
      generalize ENNReal.ofReal r25 = s25
      generalize ENNReal.ofReal r14 = s14
      generalize ENNReal.ofReal r45 = s45
      generalize ENNReal.ofReal r15 = s15
      generalize rawInterval 0 g.u = μ0
      generalize rawInterval g.u g.w = μ1
      generalize rawInterval g.w g.d = μ2
      simp only [add_zero, add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal (1 / g.d) • rawInterval 0 g.d := by
      try rw [hec0]
      try rw [hec1]
      try rw [hec2]
      rw [rawInterval_scaled_glue_three ho0 ho1 ho2]
    _ = _ := by
      exact (uniformLaw_density hd).symm

/-- Exact z-coordinate law of the third table, including collapsed pieces. -/
theorem third_marginal_z (g : ThreeGeometry) (huw : g.u ≤ g.w) :
    (marginal (g.tableLaw g.thirdWeights (g.thirdWeights_nonnegative huw)
      g.thirdWeights_mass) 2 : Measure ℝ) = zeroUniformLaw g.c g.mixtureProbability := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  rcases g.lengths_positive with ⟨ha, hd, hc, hE, hF⟩
  have hq := g.thirdWeights_nonnegative huw
  rcases hq with ⟨hq13, hq14, hq15, hq24, hq25, hq26, hq36, hq45, hq46⟩
  have hwu := sub_nonneg.mpr huw
  have hwv := sub_nonneg.mpr (le_trans g.ordered huw)
  have ho0 : 0 ≤ g.u := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  have ho1 : g.u ≤ g.c := by
    try dsimp [a, d, c, E, F, G]
    linarith [g.ordered]
  let r14 : ℝ := g.thirdWeights.q14 / g.c
  have hr14 : 0 ≤ r14 := by dsimp [r14, G, R, S]; positivity
  have hm14 : g.thirdWeights.q14 = (g.c - 0) * r14 := by
    dsimp [r14, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he14 : ENNReal.ofReal (g.thirdWeights.q14) •
      (affineUniform g.c 0 : Measure ℝ) =
        ENNReal.ofReal r14 • rawInterval 0 g.c := by
    rw [hm14]
    apply weighted_affine_interval_reverse (by linarith) hr14
  let r15 : ℝ := g.thirdWeights.q15 / g.c
  have hr15 : 0 ≤ r15 := by dsimp [r15, G, R, S]; positivity
  have hm15 : g.thirdWeights.q15 = (g.c - 0) * r15 := by
    dsimp [r15, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he15 : ENNReal.ofReal (g.thirdWeights.q15) •
      (affineUniform g.c 0 : Measure ℝ) =
        ENNReal.ofReal r15 • rawInterval 0 g.c := by
    rw [hm15]
    apply weighted_affine_interval_reverse (by linarith) hr15
  let r24 : ℝ := g.thirdWeights.q24 / g.c
  have hr24 : 0 ≤ r24 := by dsimp [r24, G, R, S]; positivity
  have hm24 : g.thirdWeights.q24 = (g.c - 0) * r24 := by
    dsimp [r24, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he24 : ENNReal.ofReal (g.thirdWeights.q24) •
      (affineUniform g.c 0 : Measure ℝ) =
        ENNReal.ofReal r24 • rawInterval 0 g.c := by
    rw [hm24]
    apply weighted_affine_interval_reverse (by linarith) hr24
  let r25 : ℝ := g.thirdWeights.q25 / g.c
  have hr25 : 0 ≤ r25 := by dsimp [r25, G, R, S]; positivity
  have hm25 : g.thirdWeights.q25 = (g.c - 0) * r25 := by
    dsimp [r25, thirdWeights]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have he25 : ENNReal.ofReal (g.thirdWeights.q25) •
      (affineUniform g.c 0 : Measure ℝ) =
        ENNReal.ofReal r25 • rawInterval 0 g.c := by
    rw [hm25]
    apply weighted_affine_interval_reverse (by linarith) hr25
  have hc0 : r14 + r15 + r24 + r25 = g.mixtureProbability / g.c := by
    dsimp [r14, r15, r24, r25, thirdWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec0 : ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r24 + ENNReal.ofReal r25 = ENNReal.ofReal (g.mixtureProbability / g.c) := by
    rw [← ENNReal.ofReal_add hr14 hr15, ← ENNReal.ofReal_add (add_nonneg hr14 hr15) hr24, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr14 hr15) hr24) hr25]
    rw [hc0]
  have hc1 : r14 + r15 + r24 + r25 = g.mixtureProbability / g.c := by
    dsimp [r14, r15, r24, r25, thirdWeights, mixtureProbability]
    field_simp [ne_of_gt ha, ne_of_gt hd, ne_of_gt hc, ne_of_gt hE, ne_of_gt hF] ;
      (try dsimp [a, d, c, E, F, G, R, S]) ; ring
  have hec1 : ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r24 + ENNReal.ofReal r25 = ENNReal.ofReal (g.mixtureProbability / g.c) := by
    rw [← ENNReal.ofReal_add hr14 hr15, ← ENNReal.ofReal_add (add_nonneg hr14 hr15) hr24, ← ENNReal.ofReal_add (add_nonneg (add_nonneg hr14 hr15) hr24) hr25]
    rw [hc1]
  have hs02 : rawInterval 0 g.c = rawInterval 0 g.u + rawInterval g.u g.c :=
    (rawInterval_glue ho0 ho1).symm
  rw [g.tableLaw_marginal]
  simp [SegmentWeights.vector, threeEdges, vertex, Fin.sum_univ_succ]
  simp only [show g.thirdWeights.q13 = 0 from rfl, show g.thirdWeights.q26 = 0 from rfl, show g.thirdWeights.q36 = 0 from rfl, show g.thirdWeights.q46 = 0 from rfl, ENNReal.ofReal_zero, zero_smul, zero_add]
  rw [he14, he15, he24, he25, affineUniform_constant]
  calc
    _ = ENNReal.ofReal (g.thirdWeights.q45) • Measure.dirac 0 + (ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r24 + ENNReal.ofReal r25) • rawInterval 0 g.u + (ENNReal.ofReal r14 + ENNReal.ofReal r15 + ENNReal.ofReal r24 + ENNReal.ofReal r25) • rawInterval g.u g.c := by
      simp only [hs02,smul_add,add_smul]
      generalize ENNReal.ofReal r14 = s14
      generalize ENNReal.ofReal r15 = s15
      generalize ENNReal.ofReal r24 = s24
      generalize ENNReal.ofReal r25 = s25
      generalize rawInterval 0 g.u = μ0
      generalize rawInterval g.u g.c = μ1
      simp only [zero_add, add_assoc, add_left_comm, add_comm]
    _ = ENNReal.ofReal (g.thirdWeights.q45) • Measure.dirac 0 + ENNReal.ofReal (g.mixtureProbability / g.c) • rawInterval 0 g.c := by
      try rw [hec0]
      try rw [hec1]
      simpa only [add_assoc] using
        congrArg (fun μ : Measure ℝ => ENNReal.ofReal (g.thirdWeights.q45) • Measure.dirac 0 + μ)
          (rawInterval_scaled_glue (d := g.mixtureProbability / g.c) ho0 ho1)
    _ = _ := by
      exact g.target_z_density.symm

end ThreeGeometry
end Blotto
