import Blotto.RationalNestedFamily
import Blotto.NestedDyadicFamilies

/-! Native numeric residual table for the middle nested case. All three
weights and vertices decode to the maintained residual law exactly. -/

namespace Blotto
open scoped BigOperators

theorem NestedResidual.eq_of_data (r s : NestedResidual) (hg : r.g = s.g) (ht : r.t = s.t) : r = s := by
  cases r
  cases s
  cases hg
  cases ht
  rfl

structure RationalNestedResidual where
  g : RationalThreeGeometry
  t : ℚ
  h_pos : 0 < g.h
  v_lt : g.v < t
  lt_u : t < g.u

namespace RationalNestedResidual

noncomputable def real (r : RationalNestedResidual) : NestedResidual where
  g := r.g.real
  t := r.t
  h_pos := by change (0 : ℝ) < (r.g.h : ℝ); exact_mod_cast r.h_pos
  v_lt := by change (r.g.v : ℝ) < (r.t : ℝ); exact_mod_cast r.v_lt
  lt_u := by change (r.t : ℝ) < (r.g.u : ℝ); exact_mod_cast r.lt_u

def s (r : RationalNestedResidual) : ℚ := r.g.u - r.t
def K (r : RationalNestedResidual) : ℚ := r.g.G * r.g.d + r.g.w * r.s
def weight (r : RationalNestedResidual) : Fin 3 → ℚ :=
  ![r.g.w * r.s / r.K, r.g.G * (r.g.d - r.s) / r.K, r.g.G * r.s / r.K]
def vertex (r : RationalNestedResidual) : Fin 3 → Fin 3 → ℚ :=
  ![![0, r.g.d, r.g.v], ![r.g.w, 0, r.g.c], ![r.g.a, r.s, r.t]]
def edges : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

theorem weight_real (r : RationalNestedResidual) : (fun slot => (r.weight slot : ℝ)) = r.real.weight := by
  funext slot
  fin_cases slot <;> simp [weight, s, K, real, RationalThreeGeometry.G, RationalThreeGeometry.d,
    RationalThreeGeometry.real, NestedResidual.weight, NestedResidual.s, NestedResidual.K,
    ThreeGeometry.G, ThreeGeometry.d]

theorem vertex_real (r : RationalNestedResidual) (slot : Fin 3) :
    (fun j => (r.vertex slot j : ℝ)) = r.real.vertex slot := by
  funext j
  fin_cases slot <;> fin_cases j <;> simp [vertex, s, real, RationalThreeGeometry.a,
    RationalThreeGeometry.d, RationalThreeGeometry.c, RationalThreeGeometry.real,
    NestedResidual.vertex, NestedResidual.s, ThreeGeometry.a, ThreeGeometry.d, ThreeGeometry.c]

theorem weight_nonnegative (r : RationalNestedResidual) : ∀ slot, 0 ≤ r.weight slot := by
  intro slot
  have h : (0 : ℝ) ≤ r.weight slot := by
    rw [congrFun r.weight_real slot]
    exact r.real.weight_nonnegative slot
  exact_mod_cast h

theorem weight_mass (r : RationalNestedResidual) : (∑ slot, r.weight slot) = 1 := by
  have h : (∑ slot, (r.weight slot : ℝ)) = 1 := by rw [r.weight_real]; exact r.real.weight_mass
  exact_mod_cast h

def segmentLottery (r : RationalNestedResidual) : RationalSegmentLottery 3 3 :=
  ⟨r.weight, (fun slot => r.vertex (edges slot).1), (fun slot => r.vertex (edges slot).2),
    r.weight_nonnegative, r.weight_mass⟩

theorem segmentLottery_real (r : RationalNestedResidual) : r.segmentLottery.real = r.real.segmentLottery := by
  apply SegmentLottery.eq_of_fields
  · exact r.weight_real
  · funext slot
    exact r.vertex_real _
  · funext slot
    exact r.vertex_real _

end RationalNestedResidual

namespace RationalNestedInput

def residualInput (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) : RationalNestedResidual :=
  ⟨i.geometry, i.t, i.h_pos, hvt, htu⟩

theorem residualInput_real (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    (i.residualInput hvt htu).real = i.real.residualInput
      (by rw [← i.v_real]; change (i.v : ℝ) < (i.t : ℝ); exact_mod_cast hvt)
      (by rw [← i.u_real]; change (i.t : ℝ) < (i.u : ℝ); exact_mod_cast htu) := by
  apply NestedResidual.eq_of_data
  · exact i.geometry_real
  · rfl

end RationalNestedInput
end Blotto
