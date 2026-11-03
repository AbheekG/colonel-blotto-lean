import Blotto.ThreeGeometry

/-! Exact rational weight checks for all three tables of Lemma 2.2.
These prove nonnegativity and total mass, including boundary parameters.
Marginal distribution identities for segment push-forwards remain separate. -/

namespace Blotto

structure SegmentWeights where
  q13 : ℝ := 0
  q14 : ℝ := 0
  q15 : ℝ := 0
  q24 : ℝ := 0
  q25 : ℝ := 0
  q26 : ℝ := 0
  q36 : ℝ := 0
  q45 : ℝ := 0
  q46 : ℝ := 0

namespace SegmentWeights

noncomputable def mass (q : SegmentWeights) : ℝ :=
  q.q13 + q.q14 + q.q15 + q.q24 + q.q25 + q.q26 + q.q36 + q.q45 + q.q46

def Nonnegative (q : SegmentWeights) : Prop :=
  0 ≤ q.q13 ∧ 0 ≤ q.q14 ∧ 0 ≤ q.q15 ∧ 0 ≤ q.q24 ∧ 0 ≤ q.q25 ∧
  0 ≤ q.q26 ∧ 0 ≤ q.q36 ∧ 0 ≤ q.q45 ∧ 0 ≤ q.q46

end SegmentWeights

namespace ThreeGeometry

/-- Exactly the potentially collapsed projections of edges other than P4P5.
Other first/second/third projection lengths are a,c,d,E,F,u, already positive.
The intentional third-coordinate atom on P4P5 is handled by atom_weight. -/
def CollapsedProjectionWeightsZero (g : ThreeGeometry) (q : SegmentWeights) : Prop :=
  ((g.w = 0 ∨ g.G = 0) → q.q13 = 0) ∧
  (g.u = g.w → q.q14 = 0) ∧ (g.v = 0 → q.q15 = 0) ∧
  (g.G = 0 → q.q24 = 0) ∧ (g.v = g.w → q.q25 = 0) ∧
  (g.w = 0 → q.q26 = 0) ∧ (g.u = g.v → q.q36 = 0) ∧
  (g.v = 0 → q.q46 = 0)

noncomputable def R (g : ThreeGeometry) : ℝ :=
  g.h ^ 2 + g.h * (g.u + g.w) + g.w * (g.u + g.v)

noncomputable def S (g : ThreeGeometry) : ℝ :=
  g.h ^ 3 + (g.u + g.v + g.w) * g.h ^ 2 +
    (g.u * g.v + g.u * g.w + g.v * g.w) * g.h +
    g.u * g.v * g.w + g.v ^ 2 * g.w

noncomputable def firstWeights (g : ThreeGeometry) : SegmentWeights where
  q13 := g.w * g.G * g.R / (g.a * g.c * g.E * g.F)
  q14 := (g.u - g.w) * g.G * g.R / (g.a * g.c * g.E * g.F)
  q25 := (g.v - g.w) * g.h / (g.c * g.E)
  q26 := g.w * g.h / (g.c * g.E)
  q36 := g.w * (g.u - g.v) * g.R / (g.a * g.c * g.E * g.F)
  q45 := g.h / g.c
  q46 := g.v * g.w * (g.u + g.v + 2 * g.h) / (g.a * g.c * g.F)

noncomputable def secondWeights (g : ThreeGeometry) : SegmentWeights where
  q13 := g.w * g.G / (g.a * g.F)
  q14 := (g.u - g.w) * g.S / (g.a * g.c * g.E * g.F)
  q15 := g.v * g.h / (g.c * g.E)
  q36 := g.w * (g.u - g.v) / (g.a * g.F)
  q45 := g.h / g.c
  q46 := g.v * g.w / (g.a * g.F)

noncomputable def thirdWeights (g : ThreeGeometry) : SegmentWeights where
  q14 := g.v * (g.w - g.u) / (g.c * g.E)
  q15 := g.v * g.F / (g.c * g.E)
  q24 := g.u * g.G / (g.c * g.E)
  q25 := g.u * (g.w - g.v) / (g.c * g.E)
  q45 := g.h / g.c

theorem firstWeights_mass (g : ThreeGeometry) : g.firstWeights.mass = 1 := by
  have ha := ne_of_gt g.lengths_positive.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  dsimp only [SegmentWeights.mass, firstWeights]
  field_simp [ha, hc, hE, hF]
  dsimp [R, a, c, E, F, G]
  ring

theorem secondWeights_mass (g : ThreeGeometry) : g.secondWeights.mass = 1 := by
  have ha := ne_of_gt g.lengths_positive.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  dsimp only [SegmentWeights.mass, secondWeights]
  field_simp [ha, hc, hE, hF]
  dsimp [S, a, c, E, F, G]
  ring

theorem thirdWeights_mass (g : ThreeGeometry) : g.thirdWeights.mass = 1 := by
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  dsimp only [SegmentWeights.mass, thirdWeights]
  field_simp [hc, hE]
  dsimp [c, E, F, G]
  ring

theorem firstWeights_nonnegative (g : ThreeGeometry) (hwv : g.w ≤ g.v) :
    g.firstWeights.Nonnegative := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  have hvw := sub_nonneg.mpr hwv
  have huw := sub_nonneg.mpr (le_trans hwv g.ordered)
  have hlen := g.lengths_positive
  rcases hlen with ⟨ha, hd, hc, hE, hF⟩
  dsimp [SegmentWeights.Nonnegative, firstWeights, G, R]
  repeat' constructor
  all_goals positivity

theorem secondWeights_nonnegative (g : ThreeGeometry) (hwu : g.w ≤ g.u) :
    g.secondWeights.Nonnegative := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  have huv := sub_nonneg.mpr g.ordered
  have huw := sub_nonneg.mpr hwu
  have hlen := g.lengths_positive
  rcases hlen with ⟨ha, hd, hc, hE, hF⟩
  dsimp [SegmentWeights.Nonnegative, secondWeights, G, S]
  repeat' constructor
  all_goals positivity

theorem thirdWeights_nonnegative (g : ThreeGeometry) (huw : g.u ≤ g.w) :
    g.thirdWeights.Nonnegative := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hh := g.h_nonneg
  have hwu := sub_nonneg.mpr huw
  have hwv := sub_nonneg.mpr (le_trans g.ordered huw)
  have hlen := g.lengths_positive
  rcases hlen with ⟨ha, hd, hc, hE, hF⟩
  dsimp [SegmentWeights.Nonnegative, thirdWeights, G]
  repeat' constructor
  all_goals positivity

theorem firstWeights_collapsed (g : ThreeGeometry) :
    g.CollapsedProjectionWeightsZero g.firstWeights := by
  simp (config := {contextual := true}) [CollapsedProjectionWeightsZero, firstWeights]

theorem secondWeights_collapsed (g : ThreeGeometry) :
    g.CollapsedProjectionWeightsZero g.secondWeights := by
  simp (config := {contextual := true}) [CollapsedProjectionWeightsZero, secondWeights]

theorem thirdWeights_collapsed (g : ThreeGeometry) :
    g.CollapsedProjectionWeightsZero g.thirdWeights := by
  simp (config := {contextual := true}) [CollapsedProjectionWeightsZero, thirdWeights]

end ThreeGeometry
end Blotto
