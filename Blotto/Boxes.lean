import Blotto.Segments
import Blotto.ThreeCoupling

/-! Coordinate boxes for actual laws and every segment output. These bounds
are needed when a construction reflects a coordinate as L-x. -/

namespace Blotto
open MeasureTheory Set Filter

def InBox {n : ℕ} (length : Allocation n) (x : Allocation n) : Prop :=
  ∀ j, 0 ≤ x j ∧ x j ≤ length j

theorem segment_inBox {n : ℕ} {length P Q : Allocation n} {t : ℝ}
    (hP : InBox length P) (hQ : InBox length Q) (ht : 0 ≤ t ∧ t ≤ 1) :
    InBox length (segmentPoint P Q t) := by
  intro j
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hP j).1)
      (mul_nonneg ht.1 (hQ j).1)
  · have h1 := mul_le_mul_of_nonneg_left (hP j).2 (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left (hQ j).2 ht.1
    dsimp [segmentPoint]
    nlinarith

theorem measurable_inBox {n : ℕ} (length : Allocation n) : MeasurableSet {x | InBox length x} := by
  have he : {x : Allocation n | InBox length x} =
      ⋂ j : Fin n, {x | x j ∈ Icc 0 (length j)} := by ext x; simp [InBox]
  rw [he]
  exact MeasurableSet.iInter fun j => measurableSet_Icc.preimage (measurable_pi_apply j)

theorem law_inBox_of_marginals {n : ℕ} (μ : Mixed n) (length : Allocation n)
    (h : ∀ j, ∀ᵐ t ∂(marginal μ j : Measure ℝ), t ∈ Icc 0 (length j)) :
    ∀ᵐ x ∂(μ : Measure (Allocation n)), InBox length x := by
  have hj : ∀ j, ∀ᵐ x ∂(μ : Measure (Allocation n)), x j ∈ Icc 0 (length j) := by
    intro j
    have hm := h j
    change ∀ᵐ t ∂Measure.map (fun x : Allocation n => x j) (μ : Measure (Allocation n)),
      0 ≤ t ∧ t ≤ length j at hm
    exact (ae_map_iff (measurable_pi_apply j).aemeasurable measurableSet_Icc).mp hm
  exact (ae_all_iff.mpr hj)

namespace ThreeGeometry

theorem vertex_inBox (g : ThreeGeometry) (k : Fin 6) :
    InBox ![g.a, g.d, g.c] (g.vertex k) := by
  have hu := g.u_pos
  have hv := g.v_nonneg
  have hw := g.w_nonneg
  have hh := g.h_nonneg
  intro j
  fin_cases k <;> fin_cases j
  all_goals simp [vertex, a, d, c]
  all_goals try constructor
  all_goals linarith

theorem couplingPoint_inBox (g : ThreeGeometry) (edge : Fin 9) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : InBox ![g.a, g.d, g.c] (g.couplingPoint edge t) :=
  segment_inBox (g.vertex_inBox _) (g.vertex_inBox _) ht

end ThreeGeometry
end Blotto
