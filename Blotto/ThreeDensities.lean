import Blotto.ThreeWeights

/-! All displayed continuous-density identities from manuscript Lemma 2.2.
Each division by an interval length is guarded by strict positivity of that
length. These are algebraic identities; measure-level marginal equality is
still an additional proof obligation. -/

namespace Blotto.ThreeGeometry

theorem first_x_density (g : ThreeGeometry) :
    (g.firstWeights.q13 + g.firstWeights.q14 + g.firstWeights.q36 + g.firstWeights.q46) / g.a + g.h / (g.c * g.E) = 1 / g.a := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [firstWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem first_y_low_density (g : ThreeGeometry) (hw : 0 < g.w):
    (g.firstWeights.q25 + g.firstWeights.q26 + g.firstWeights.q36) / g.d + g.firstWeights.q13 / g.w = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [firstWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hw]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem first_y_middle_density (g : ThreeGeometry) (huw : 0 < g.u - g.w):
    (g.firstWeights.q25 + g.firstWeights.q26 + g.firstWeights.q36) / g.d + g.firstWeights.q14 / (g.u - g.w) = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [firstWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt huw]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem first_y_high_density (g : ThreeGeometry) :
    (g.firstWeights.q25 + g.firstWeights.q26 + g.firstWeights.q36) / g.d + (g.firstWeights.q45 + g.firstWeights.q46) / g.E = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [firstWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem first_z_low_density (g : ThreeGeometry) (hv : 0 < g.v):
    (g.firstWeights.q14 + g.firstWeights.q25) / g.c + g.firstWeights.q46 / g.v = g.mixtureProbability / g.c := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [firstWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hv]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem first_z_middle_density (g : ThreeGeometry) (huv : 0 < g.u - g.v):
    (g.firstWeights.q14 + g.firstWeights.q25) / g.c + g.firstWeights.q26 / g.F + g.firstWeights.q36 / (g.u - g.v) = g.mixtureProbability / g.c := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [firstWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt huv]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem first_z_high_density (g : ThreeGeometry) (hG : 0 < g.G):
    (g.firstWeights.q14 + g.firstWeights.q25) / g.c + g.firstWeights.q26 / g.F + g.firstWeights.q13 / g.G = g.mixtureProbability / g.c := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [firstWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hG]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem second_x_low_density (g : ThreeGeometry) (hv : 0 < g.v):
    (g.secondWeights.q13 + g.secondWeights.q14 + g.secondWeights.q36 + g.secondWeights.q46) / g.a + g.secondWeights.q15 / g.v = 1 / g.a := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [secondWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hv]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem second_x_high_density (g : ThreeGeometry) :
    (g.secondWeights.q13 + g.secondWeights.q14 + g.secondWeights.q36 + g.secondWeights.q46) / g.a + g.secondWeights.q45 / g.E = 1 / g.a := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [secondWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem second_y_low_density (g : ThreeGeometry) (hw : 0 < g.w):
    g.secondWeights.q36 / g.d + g.secondWeights.q13 / g.w = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [secondWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hw]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem second_y_middle_density (g : ThreeGeometry) (huw : 0 < g.u - g.w):
    g.secondWeights.q36 / g.d + g.secondWeights.q14 / (g.u - g.w) + g.secondWeights.q15 / g.F = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [secondWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt huw]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem second_y_high_density (g : ThreeGeometry) :
    g.secondWeights.q36 / g.d + g.secondWeights.q15 / g.F + (g.secondWeights.q45 + g.secondWeights.q46) / g.E = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [secondWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem second_z_low_density (g : ThreeGeometry) (hv : 0 < g.v):
    (g.secondWeights.q14 + g.secondWeights.q15) / g.c + g.secondWeights.q46 / g.v = g.mixtureProbability / g.c := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [secondWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hv]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem second_z_middle_density (g : ThreeGeometry) (huv : 0 < g.u - g.v):
    (g.secondWeights.q14 + g.secondWeights.q15) / g.c + g.secondWeights.q36 / (g.u - g.v) = g.mixtureProbability / g.c := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [secondWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt huv]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem second_z_high_density (g : ThreeGeometry) (hG : 0 < g.G):
    (g.secondWeights.q14 + g.secondWeights.q15) / g.c + g.secondWeights.q13 / g.G = g.mixtureProbability / g.c := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [secondWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hG]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem third_x_low_density (g : ThreeGeometry) (hv : 0 < g.v):
    g.thirdWeights.q14 / g.a + g.thirdWeights.q15 / g.v = 1 / g.a := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [thirdWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hv]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem third_x_middle_density (g : ThreeGeometry) (hwv : 0 < g.w - g.v):
    g.thirdWeights.q14 / g.a + g.thirdWeights.q25 / (g.w - g.v) + g.thirdWeights.q45 / g.E = 1 / g.a := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [thirdWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hwv]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem third_x_high_density (g : ThreeGeometry) (hG : 0 < g.G):
    g.thirdWeights.q14 / g.a + g.thirdWeights.q24 / g.G + g.thirdWeights.q45 / g.E = 1 / g.a := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [thirdWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hG]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem third_y_low_density (g : ThreeGeometry) :
    g.thirdWeights.q25 / g.d + g.thirdWeights.q24 / g.u = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [thirdWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem third_y_middle_density (g : ThreeGeometry) (hwu : 0 < g.w - g.u):
    g.thirdWeights.q25 / g.d + g.thirdWeights.q14 / (g.w - g.u) + g.thirdWeights.q45 / g.E = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [thirdWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu, ne_of_gt hwu]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem third_y_high_density (g : ThreeGeometry) :
    g.thirdWeights.q25 / g.d + g.thirdWeights.q15 / g.F + g.thirdWeights.q45 / g.E = 1 / g.d := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [thirdWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu]
  dsimp [a, d, c, E, F, G, R, S]
  ring

theorem third_z_density (g : ThreeGeometry) :
    (g.thirdWeights.q14 + g.thirdWeights.q15 + g.thirdWeights.q24 + g.thirdWeights.q25) / g.c = g.mixtureProbability / g.c := by
  have ha := ne_of_gt g.lengths_positive.1
  have hd := ne_of_gt g.lengths_positive.2.1
  have hc := ne_of_gt g.lengths_positive.2.2.1
  have hE := ne_of_gt g.lengths_positive.2.2.2.1
  have hF := ne_of_gt g.lengths_positive.2.2.2.2
  have hu := ne_of_gt g.u_pos
  dsimp only [thirdWeights, mixtureProbability]
  field_simp [ha, hd, hc, hE, hF, hu]
  dsimp [a, d, c, E, F, G, R, S]
  ring

end Blotto.ThreeGeometry

