import Blotto.RationalThreeGeometry

/-! Native rational versions of all three segment tables, including zero
slots. Exact cast identities transfer positivity and normalization from the
maintained real proof; no numerical checking or rational search is used. -/

namespace Blotto.RationalThreeGeometry
open scoped BigOperators

def firstWeights (g : RationalThreeGeometry) : Fin 9 → ℚ :=
  ![g.w * g.G * g.R / (g.a * g.c * g.E * g.F),
    (g.u - g.w) * g.G * g.R / (g.a * g.c * g.E * g.F), 0, 0,
    (g.v - g.w) * g.h / (g.c * g.E), g.w * g.h / (g.c * g.E),
    g.w * (g.u - g.v) * g.R / (g.a * g.c * g.E * g.F), g.h / g.c,
    g.v * g.w * (g.u + g.v + 2 * g.h) / (g.a * g.c * g.F)]

def secondWeights (g : RationalThreeGeometry) : Fin 9 → ℚ :=
  ![g.w * g.G / (g.a * g.F), (g.u - g.w) * g.S / (g.a * g.c * g.E * g.F),
    g.v * g.h / (g.c * g.E), 0, 0, 0, g.w * (g.u - g.v) / (g.a * g.F), g.h / g.c,
    g.v * g.w / (g.a * g.F)]

def thirdWeights (g : RationalThreeGeometry) : Fin 9 → ℚ :=
  ![0, g.v * (g.w - g.u) / (g.c * g.E), g.v * g.F / (g.c * g.E),
    g.u * g.G / (g.c * g.E), g.u * (g.w - g.v) / (g.c * g.E), 0, 0, g.h / g.c, 0]

def chosenWeights (g : RationalThreeGeometry) : Fin 9 → ℚ :=
  if g.w ≤ g.v then g.firstWeights else if g.w ≤ g.u then g.secondWeights else g.thirdWeights

theorem firstWeights_real (g : RationalThreeGeometry) :
    (fun slot => (g.firstWeights slot : ℝ)) = g.real.firstWeights.vector := by
  funext slot
  fin_cases slot <;> simp [firstWeights, a, c, E, F, G, R, real, ThreeGeometry.firstWeights,
    SegmentWeights.vector, ThreeGeometry.a, ThreeGeometry.c, ThreeGeometry.E, ThreeGeometry.F,
    ThreeGeometry.G, ThreeGeometry.R]

theorem secondWeights_real (g : RationalThreeGeometry) :
    (fun slot => (g.secondWeights slot : ℝ)) = g.real.secondWeights.vector := by
  funext slot
  fin_cases slot <;> simp [secondWeights, a, c, E, F, G, S, real, ThreeGeometry.secondWeights,
    SegmentWeights.vector, ThreeGeometry.a, ThreeGeometry.c, ThreeGeometry.E, ThreeGeometry.F,
    ThreeGeometry.G, ThreeGeometry.S]

theorem thirdWeights_real (g : RationalThreeGeometry) :
    (fun slot => (g.thirdWeights slot : ℝ)) = g.real.thirdWeights.vector := by
  funext slot
  fin_cases slot <;> simp [thirdWeights, c, E, F, G, real, ThreeGeometry.thirdWeights,
    SegmentWeights.vector, ThreeGeometry.c, ThreeGeometry.E, ThreeGeometry.F, ThreeGeometry.G]

theorem chosenWeights_real (g : RationalThreeGeometry) :
    (fun slot => (g.chosenWeights slot : ℝ)) = g.real.chosenWeights.vector := by
  have h1 : g.w ≤ g.v ↔ g.real.w ≤ g.real.v := by dsimp [real]; norm_cast
  have h2 : g.w ≤ g.u ↔ g.real.w ≤ g.real.u := by dsimp [real]; norm_cast
  unfold chosenWeights ThreeGeometry.chosenWeights
  by_cases hwv : g.w ≤ g.v
  · rw [ite_eq_left hwv, ite_eq_left (h1.mp hwv)]
    exact g.firstWeights_real
  · rw [ite_eq_right hwv, ite_eq_right (fun h => hwv (h1.mpr h))]
    by_cases hwu : g.w ≤ g.u
    · rw [ite_eq_left hwu, ite_eq_left (h2.mp hwu)]
      exact g.secondWeights_real
    · rw [ite_eq_right hwu, ite_eq_right (fun h => hwu (h2.mpr h))]
      exact g.thirdWeights_real

theorem chosenWeights_nonnegative (g : RationalThreeGeometry) : ∀ slot, 0 ≤ g.chosenWeights slot := by
  have hr : ∀ slot, (0 : ℝ) ≤ g.chosenWeights slot := by
    intro slot
    rw [show (g.chosenWeights slot : ℝ) = g.real.chosenWeights.vector slot from congrFun g.chosenWeights_real slot]
    exact g.real.chosenWeights.vector_nonnegative g.real.chosenWeights_nonnegative slot
  intro slot
  exact_mod_cast hr slot

theorem chosenWeights_mass (g : RationalThreeGeometry) : (∑ slot, g.chosenWeights slot) = 1 := by
  have hr : (∑ slot, (g.chosenWeights slot : ℝ)) = 1 := by
    rw [g.chosenWeights_real, g.real.chosenWeights.vector_mass, g.real.chosenWeights_mass]
  exact_mod_cast hr

def segmentLottery (g : RationalThreeGeometry) : RationalSegmentLottery 3 9 :=
  ⟨g.chosenWeights, (fun slot => g.vertex (edges slot).1), (fun slot => g.vertex (edges slot).2),
    g.chosenWeights_nonnegative, g.chosenWeights_mass⟩

theorem segmentLottery_real (g : RationalThreeGeometry) : g.segmentLottery.real = g.real.segmentLottery := by
  have hw := g.chosenWeights_real
  have hP : (fun slot j => (g.vertex (edges slot).1 j : ℝ)) = fun slot => g.real.vertex (threeEdges slot).1 := by
    funext slot
    rw [edges_real]
    exact g.vertex_real _
  have hQ : (fun slot j => (g.vertex (edges slot).2 j : ℝ)) = fun slot => g.real.vertex (threeEdges slot).2 := by
    funext slot
    rw [edges_real]
    exact g.vertex_real _
  exact SegmentLottery.eq_of_fields _ _ hw hP hQ

end Blotto.RationalThreeGeometry
