import Blotto.ThreeBoxes
import Blotto.NestedCoupling

/-! Coordinate ranges of every nested-coupling output path. These strengthen
the budget-only statements needed for subsequent nonnegative reflection. -/

namespace Blotto
open MeasureTheory Set

theorem inBox_mono {n : ℕ} {a b x : Allocation n} (hab : ∀ j, a j ≤ b j)
    (hx : InBox a x) : InBox b x := fun j => ⟨(hx j).1, le_trans (hx j).2 (hab j)⟩

theorem shiftThird_inBox {a d c s : ℝ} {x : Allocation 3} (hs : 0 ≤ s)
    (hx : InBox ![a, d, c] x) : InBox ![a, d, c + s] (shiftThird s x) := by
  intro j
  fin_cases j
  · exact hx 0
  · exact hx 1
  · have hz := hx 2
    change 0 ≤ x 2 ∧ x 2 ≤ c at hz
    change 0 ≤ x 2 + s ∧ x 2 + s ≤ c + s
    exact ⟨add_nonneg hz.1 hs, by linarith [hz.2]⟩

namespace NestedResidual

theorem vertex_inBox (r : NestedResidual) (i : Fin 3) :
    InBox ![r.g.a, r.g.d, r.g.c] (r.vertex i) := by
  have hv := r.g.v_nonneg
  have hw := r.g.w_nonneg
  have hu := r.g.u_pos
  have hh := r.h_pos
  have ht := r.lt_u
  have hp := r.parameters
  intro j
  fin_cases i <;> fin_cases j
  all_goals simp [vertex, s, ThreeGeometry.a, ThreeGeometry.d, ThreeGeometry.c]
  all_goals try constructor
  all_goals linarith [r.v_lt]

theorem point_inBox (r : NestedResidual) (i : Fin 3) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    InBox ![r.g.a, r.g.d, r.g.c]
      (segmentPoint (r.vertex (edges i).1) (r.vertex (edges i).2) t) :=
  segment_inBox (r.vertex_inBox _) (r.vertex_inBox _) ht

end NestedResidual

namespace NestedInput

theorem firstPoint_inBox (i : NestedInput) (htv : i.t ≤ i.v) {s t : ℝ}
    (hs : 0 ≤ s ∧ s ≤ i.t) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) :
    InBox ![i.a, i.d, i.c] (i.firstPoint htv s edge t) := by
  classical
  unfold firstPoint
  split_ifs with hp
  · have he := i.firstGeometry_matches htv s hp.1 hp.2
    have hb := (i.firstGeometry htv s hp.1 hp.2).couplingPoint_inBox edge ht
    have ha : InBox ![i.a, i.d, i.c - s]
        ((i.firstGeometry htv s hp.1 hp.2).couplingPoint edge t) := by
      simpa only [he.1, he.2.1, he.2.2.1] using hb
    simpa only [sub_add_cancel] using shiftThird_inBox hs.1 ha
  · apply segment_inBox _ _ ht
    · intro j
      fin_cases j
      · exact ⟨le_rfl, le_of_lt i.a_pos⟩
      · exact ⟨le_of_lt i.d_pos, le_rfl⟩
      · exact ⟨hs.1, le_trans hs.2 (le_of_lt i.t_lt)⟩
    · intro j
      fin_cases j
      · exact ⟨le_of_lt i.a_pos, le_rfl⟩
      · exact ⟨le_rfl, le_of_lt i.d_pos⟩
      · exact ⟨hs.1, le_trans hs.2 (le_of_lt i.t_lt)⟩

theorem firstSamplePath_inBox (i : NestedInput) (htv : i.t ≤ i.v) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) :
    InBox ![i.a, i.d, i.c] (i.firstPoint htv (i.location r) edge t) :=
  i.firstPoint_inBox htv (i.location_bounds hr) ht edge

theorem familyFirstPoint_inBox (i : NestedInput) (x : ℝ) (hx0 : 0 < x) (hxv : x ≤ i.v)
    {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) :
    InBox ![i.a, i.d, i.c] (i.familyFirstPoint x hx0 hxv r edge t) :=
  (i.atLength x hx0 (by linarith [i.lengths.2.2.1])).firstSamplePath_inBox hxv hr ht edge

theorem secondPoint_inBox (i : NestedInput) (htu : i.u ≤ i.t) (useFamily : Bool)
    {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) :
    InBox ![i.a, i.d, i.c] (i.secondPoint htu useFamily r t edge) := by
  unfold secondPoint
  split_ifs with hTt hFamily
  · exact i.familyFirstPoint_inBox _ _ _ hr ht edge
  · have hs : InBox ![i.a, i.d, i.t - i.mirrorLength]
        ((i.secondUniformInput htu hTt).couplingPoint edge t) :=
      (i.secondUniformInput htu hTt).couplingPoint_inBox edge ht
    have hb : InBox ![i.a, i.d, i.t]
        (shiftThird i.mirrorLength ((i.secondUniformInput htu hTt).couplingPoint edge t)) := by
      simpa only [sub_add_cancel] using shiftThird_inBox (le_of_lt (i.mirrorLength_bounds htu).1) hs
    apply inBox_mono _ hb
    intro j
    fin_cases j
    · exact le_rfl
    · exact le_rfl
    · exact le_of_lt i.t_lt
  · exact i.familyFirstPoint_inBox _ _ _ hr ht edge

theorem thirdPoint_inBox (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (useFamily : Bool) {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (edge : Fin 9) (residualEdge : Fin 3) :
    InBox ![i.a, i.d, i.c] (i.thirdPoint hvt htu useFamily r t edge residualEdge) := by
  have he := i.geometry_matches
  have hb : InBox ![i.a, i.d, i.c]
      (segmentPoint ((i.residualInput hvt htu).vertex (NestedResidual.edges residualEdge).1)
        ((i.residualInput hvt htu).vertex (NestedResidual.edges residualEdge).2) t) := by
    simpa only [residualInput, he.1, he.2.1, he.2.2.1] using
      (i.residualInput hvt htu).point_inBox residualEdge ht
  unfold thirdPoint
  split_ifs
  · exact i.familyFirstPoint_inBox _ _ _ hr ht edge
  · exact hb
  · exact hb

theorem couplingPoint_inBox (i : NestedInput) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) (residualEdge : Fin 3) :
    InBox ![i.a, i.d, i.c] (i.couplingPoint useFamily r t edge residualEdge) := by
  unfold couplingPoint
  split_ifs with htv htu
  · exact i.firstSamplePath_inBox htv hr ht edge
  · exact i.secondPoint_inBox htu useFamily hr ht edge
  · exact i.thirdPoint_inBox (lt_of_not_ge htv) (lt_of_not_ge htu) useFamily hr ht edge residualEdge

end NestedInput
end Blotto
