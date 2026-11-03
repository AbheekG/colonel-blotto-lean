import Blotto.ThreeLottery
import Blotto.RationalSegmentLottery

/-! Computable rational parameters and vertices of the three-variable
coupling, with an exact interpretation in the proved real geometry. -/

namespace Blotto

structure RationalThreeGeometry where
  u : ℚ
  v : ℚ
  w : ℚ
  h : ℚ
  u_pos : 0 < u
  v_nonneg : 0 ≤ v
  w_nonneg : 0 ≤ w
  h_nonneg : 0 ≤ h
  ordered : v ≤ u
  a_pos : 0 < v + w + h
  E_pos : 0 < w + h

namespace RationalThreeGeometry

def a (g : RationalThreeGeometry) : ℚ := g.v + g.w + g.h
def d (g : RationalThreeGeometry) : ℚ := g.u + g.w + g.h
def c (g : RationalThreeGeometry) : ℚ := g.u + g.v + g.h
def budget (g : RationalThreeGeometry) : ℚ := g.u + g.v + g.w + g.h
def E (g : RationalThreeGeometry) : ℚ := g.w + g.h
def F (g : RationalThreeGeometry) : ℚ := g.u + g.h
def G (g : RationalThreeGeometry) : ℚ := g.v + g.h
def R (g : RationalThreeGeometry) : ℚ := g.h ^ 2 + g.h * (g.u + g.w) + g.w * (g.u + g.v)
def S (g : RationalThreeGeometry) : ℚ := g.h ^ 3 + (g.u + g.v + g.w) * g.h ^ 2 +
  (g.u * g.v + g.u * g.w + g.v * g.w) * g.h + g.u * g.v * g.w + g.v ^ 2 * g.w

noncomputable def real (g : RationalThreeGeometry) : ThreeGeometry where
  u := g.u
  v := g.v
  w := g.w
  h := g.h
  u_pos := by exact_mod_cast g.u_pos
  v_nonneg := by exact_mod_cast g.v_nonneg
  w_nonneg := by exact_mod_cast g.w_nonneg
  h_nonneg := by exact_mod_cast g.h_nonneg
  ordered := by exact_mod_cast g.ordered
  a_pos := by exact_mod_cast g.a_pos
  E_pos := by exact_mod_cast g.E_pos

def vertex (g : RationalThreeGeometry) : Fin 6 → Fin 3 → ℚ :=
  ![![0, g.w, g.c], ![g.w, 0, g.c], ![g.a, 0, g.u],
    ![g.a, g.u, 0], ![g.v, g.d, 0], ![0, g.d, g.v]]

def edges : Fin 9 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (2, 5), (3, 4), (3, 5)]

theorem edges_real : edges = threeEdges := rfl

theorem vertex_real (g : RationalThreeGeometry) (slot : Fin 6) :
    (fun j => (g.vertex slot j : ℝ)) = g.real.vertex slot := by
  funext j
  fin_cases slot <;> fin_cases j <;>
    simp [vertex, a, d, c, real, ThreeGeometry.vertex, ThreeGeometry.a, ThreeGeometry.d, ThreeGeometry.c]

theorem budget_real (g : RationalThreeGeometry) : (g.budget : ℝ) = g.real.budget := by
  simp [budget, real, ThreeGeometry.budget]

end RationalThreeGeometry
end Blotto
