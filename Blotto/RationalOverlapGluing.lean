import Blotto.RationalSegmentLottery
import Blotto.OverlapBudget

/-! Native rational pairwise overlap gluing with the four-variable probes.
All interval endpoints, inverse parameters, weights and safe segment endpoints
are computed from the two source descriptors. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

structure RationalOverlapGluing (k h : ℕ) where
  first : RationalSegmentLottery 3 k
  second : RationalSegmentLottery 3 h
  d : ℚ
  d_pos : 0 < d
  first_uniform : Measure.map (fun x : Allocation 3 => x 2) (first.real.law : Measure (Allocation 3)) = uniformLaw (d : ℝ)
  second_uniform : Measure.map (fun x : Allocation 3 => (d : ℝ) - x 0) (second.real.law : Measure (Allocation 3)) = uniformLaw (d : ℝ)
  first_P_range : ∀ i, 0 ≤ first.P i 2 ∧ first.P i 2 ≤ d
  first_Q_range : ∀ i, 0 ≤ first.Q i 2 ∧ first.Q i 2 ≤ d

namespace RationalOverlapGluing

noncomputable def real {k h : ℕ} (G : RationalOverlapGluing k h) : OverlapGluing k h where
  first := G.first.real
  second := G.second.real
  firstProbe := AffineProbe.coordinate 2
  secondProbe := AffineProbe.reflectedCoordinate G.d 0
  d := G.d
  d_pos := by exact_mod_cast G.d_pos
  first_uniform := G.first_uniform
  second_uniform := G.second_uniform
  first_P_range := fun i => by
    change (0 : ℝ) ≤ (G.first.P i 2 : ℝ) ∧ (G.first.P i 2 : ℝ) ≤ (G.d : ℝ)
    exact_mod_cast G.first_P_range i
  first_Q_range := fun i => by
    change (0 : ℝ) ≤ (G.first.Q i 2 : ℝ) ∧ (G.first.Q i 2 : ℝ) ≤ (G.d : ℝ)
    exact_mod_cast G.first_Q_range i

def lower {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) : ℚ :=
  max (min (G.first.P i 2) (G.first.Q i 2)) (min (G.d - G.second.P j 0) (G.d - G.second.Q j 0))

def upper {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) : ℚ :=
  min (max (G.first.P i 2) (G.first.Q i 2)) (max (G.d - G.second.P j 0) (G.d - G.second.Q j 0))

def weight {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) : ℚ :=
  G.d * G.first.weight i * G.second.weight j * max (G.upper i j - G.lower i j) 0 /
    (|G.first.Q i 2 - G.first.P i 2| * |(G.d - G.second.Q j 0) - (G.d - G.second.P j 0)|)

def curve {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) (z : ℚ) : Fin 4 → ℚ :=
  let x := rationalSegmentPoint (G.first.P i) (G.first.Q i) ((z - G.first.P i 2) / (G.first.Q i 2 - G.first.P i 2))
  let y := rationalSegmentPoint (G.second.P j) (G.second.Q j)
    ((z - (G.d - G.second.P j 0)) / ((G.d - G.second.Q j 0) - (G.d - G.second.P j 0)))
  ![x 0, x 1, y 1, y 2]

theorem lower_real {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) :
    (G.lower i j : ℝ) = G.real.lower i j := by
  simp [lower, real, OverlapGluing.lower, overlapLower, AffineProbe.coordinate, AffineProbe.reflectedCoordinate,
    RationalSegmentLottery.real]

theorem upper_real {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) :
    (G.upper i j : ℝ) = G.real.upper i j := by
  simp [upper, real, OverlapGluing.upper, overlapUpper, AffineProbe.coordinate, AffineProbe.reflectedCoordinate,
    RationalSegmentLottery.real]

theorem weight_real {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) :
    (G.weight i j : ℝ) = G.real.weight i j := by
  rw [G.real.weight_formula]
  simp [weight, G.lower_real, G.upper_real, real, RationalSegmentLottery.real,
    AffineProbe.coordinate, AffineProbe.reflectedCoordinate]

theorem curve_real {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) (z : ℚ) :
    (fun r => (G.curve i j z r : ℝ)) = (G.real.curve i j).value z := by
  funext r
  fin_cases r <;> simp [curve, real, OverlapGluing.curve, pairGlueCurve, glueAllocation,
    SegmentLottery.pointAt, SegmentLottery.point, inverseParameter, RationalSegmentLottery.real,
    rationalSegmentPoint, segmentPoint, AffineProbe.coordinate, AffineProbe.reflectedCoordinate]

theorem weight_nonnegative {k h : ℕ} (G : RationalOverlapGluing k h) (i : Fin k) (j : Fin h) : 0 ≤ G.weight i j := by
  have h : (0 : ℝ) ≤ G.weight i j := by rw [G.weight_real]; exact G.real.weight_nonnegative i j
  exact_mod_cast h

end RationalOverlapGluing
end Blotto
