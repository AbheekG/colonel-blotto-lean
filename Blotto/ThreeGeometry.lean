import Blotto.Model

/-! Pointwise geometry of manuscript Lemma 2.2. This is a component of
the coupling proof, not a statement about the sampler's marginal laws. -/

namespace Blotto

theorem fullBudget_three {x y z B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x + y + z = B) : FullBudget B ![x, y, z] := by
  constructor
  · intro j
    fin_cases j
    · exact hx
    · exact hy
    · exact hz
  · simpa [Fin.sum_univ_succ, add_assoc] using hs

noncomputable def segmentPoint {n : ℕ} (P Q : Allocation n) (t : ℝ) : Allocation n :=
  fun j => (1 - t) * P j + t * Q j

/-- Every bit/real path with t in [0,1] stays in the full-budget plane. -/
theorem segment_fullBudget {n : ℕ} {B t : ℝ} {P Q : Allocation n}
    (hP : FullBudget B P) (hQ : FullBudget B Q) (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget B (segmentPoint P Q t) := by
  constructor
  · intro j
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hP.1 j))
      (mul_nonneg ht.1 (hQ.1 j))
  · simp only [segmentPoint, Finset.sum_add_distrib, ← Finset.mul_sum, hP.2, hQ.2]
    ring

structure ThreeGeometry where
  u : ℝ
  v : ℝ
  w : ℝ
  h : ℝ
  u_pos : 0 < u
  v_nonneg : 0 ≤ v
  w_nonneg : 0 ≤ w
  h_nonneg : 0 ≤ h
  ordered : v ≤ u
  a_pos : 0 < v + w + h
  E_pos : 0 < w + h

namespace ThreeGeometry

noncomputable def a (g : ThreeGeometry) : ℝ := g.v + g.w + g.h
noncomputable def d (g : ThreeGeometry) : ℝ := g.u + g.w + g.h
noncomputable def c (g : ThreeGeometry) : ℝ := g.u + g.v + g.h
noncomputable def budget (g : ThreeGeometry) : ℝ := g.u + g.v + g.w + g.h
noncomputable def E (g : ThreeGeometry) : ℝ := g.w + g.h
noncomputable def F (g : ThreeGeometry) : ℝ := g.u + g.h
noncomputable def G (g : ThreeGeometry) : ℝ := g.v + g.h
noncomputable def mixtureProbability (g : ThreeGeometry) : ℝ := (g.u + g.v) / g.c

theorem lengths_positive (g : ThreeGeometry) :
    0 < g.a ∧ 0 < g.d ∧ 0 < g.c ∧ 0 < g.E ∧ 0 < g.F := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  dsimp [a, d, c, E, F]
  exact ⟨g.a_pos, by linarith, by linarith, g.E_pos, by linarith⟩

theorem mixtureProbability_bounds (g : ThreeGeometry) :
    0 < g.mixtureProbability ∧ g.mixtureProbability ≤ 1 := by
  have hc := g.lengths_positive.2.2.1
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hh := g.h_nonneg
  constructor
  · exact div_pos (by linarith) hc
  · apply (div_le_one hc).mpr
    dsimp [c]
    linarith

theorem resource_identity (g : ThreeGeometry) :
    g.a + g.d + g.mixtureProbability * g.c = 2 * g.budget := by
  have hc := ne_of_gt g.lengths_positive.2.2.1
  unfold mixtureProbability
  rw [div_mul_cancel₀ _ hc]
  dsimp [a, d, budget]
  ring

theorem atom_weight (g : ThreeGeometry) :
    g.h / g.c = 1 - g.mixtureProbability := by
  have hc := ne_of_gt g.lengths_positive.2.2.1
  unfold mixtureProbability
  field_simp [hc]
  dsimp [c]
  ring

noncomputable def vertex (g : ThreeGeometry) : Fin 6 → Allocation 3 :=
  ![![0, g.w, g.c], ![g.w, 0, g.c], ![g.a, 0, g.u],
    ![g.a, g.u, 0], ![g.v, g.d, 0], ![0, g.d, g.v]]

theorem vertex_fullBudget (g : ThreeGeometry) (k : Fin 6) :
    FullBudget g.budget (g.vertex k) := by
  have hu := le_of_lt g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have ha := le_of_lt g.lengths_positive.1
  have hd := le_of_lt g.lengths_positive.2.1
  have hc := le_of_lt g.lengths_positive.2.2.1
  fin_cases k
  · exact fullBudget_three (le_refl 0) hw hc (by dsimp [budget, c]; ring)
  · exact fullBudget_three hw (le_refl 0) hc (by dsimp [budget, c]; ring)
  · exact fullBudget_three ha (le_refl 0) hu (by dsimp [budget, a]; ring)
  · exact fullBudget_three ha hu (le_refl 0) (by dsimp [budget, a]; ring)
  · exact fullBudget_three hv hd (le_refl 0) (by dsimp [budget, d]; ring)
  · exact fullBudget_three (le_refl 0) hd hv (by dsimp [budget, d]; ring)

theorem every_segment_fullBudget (g : ThreeGeometry) (k l : Fin 6) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget g.budget (segmentPoint (g.vertex k) (g.vertex l) t) :=
  segment_fullBudget (g.vertex_fullBudget k) (g.vertex_fullBudget l) ht

end ThreeGeometry

/-- The exceptional E=0 segment also respects the budget pointwise. -/
theorem three_exceptional_budget {a d B t : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hB : 0 ≤ B) (hsum : a + d = B) (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget B ![a * t, d * t, B * (1 - t)] := by
  apply fullBudget_three (mul_nonneg ha ht.1) (mul_nonneg hd ht.1)
    (mul_nonneg hB (sub_nonneg.mpr ht.2))
  nlinarith [hsum]

end Blotto
