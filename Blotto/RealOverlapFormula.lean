import Blotto.OverlapFormulaCode
import Blotto.OverlapDescriptor

/-! Real evaluation of the portable overlap expressions equals the existing
coordinate/reflected-coordinate gluing formulas, including total divisions. -/

namespace Blotto.RealOverlapFormula
open OverlapFormulaCode

noncomputable def environment {k h : ℕ} (G : OverlapGluing k h) (B : ℝ)
    (i : Fin k) (j : Fin h) : FixedArrayTable 16 ℝ :=
  FixedArrayTable.ofFn ![G.first.P i 0, G.first.P i 1, G.first.P i 2,
    G.first.Q i 0, G.first.Q i 1, G.first.Q i 2,
    G.second.P j 0, G.second.P j 1, G.second.P j 2,
    G.second.Q j 0, G.second.Q j 1, G.second.Q j 2,
    G.first.weight i, G.second.weight j, G.d, B]

@[simp] theorem firstP_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) (r : Fin 3) :
    (firstP r).realValue (environment G B i j) = G.first.P i r := by
  fin_cases r <;> simp [firstP, environment, FixedArrayTable.read_ofFn]
@[simp] theorem firstQ_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) (r : Fin 3) :
    (firstQ r).realValue (environment G B i j) = G.first.Q i r := by
  fin_cases r <;> simp [firstQ, environment, FixedArrayTable.read_ofFn]
@[simp] theorem secondP_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) (r : Fin 3) :
    (secondP r).realValue (environment G B i j) = G.second.P j r := by
  fin_cases r <;> simp [secondP, environment, FixedArrayTable.read_ofFn]
@[simp] theorem secondQ_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) (r : Fin 3) :
    (secondQ r).realValue (environment G B i j) = G.second.Q j r := by
  fin_cases r <;> simp [secondQ, environment, FixedArrayTable.read_ofFn]
@[simp] theorem firstWeight_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) :
    firstWeight.realValue (environment G B i j) = G.first.weight i := by
  simp [firstWeight, environment, FixedArrayTable.read_ofFn]
@[simp] theorem secondWeight_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) :
    secondWeight.realValue (environment G B i j) = G.second.weight j := by
  simp [secondWeight, environment, FixedArrayTable.read_ofFn]
@[simp] theorem intervalLength_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) :
    intervalLength.realValue (environment G B i j) = G.d := by
  simp [intervalLength, environment, FixedArrayTable.read_ofFn]
@[simp] theorem budget_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) :
    budget.realValue (environment G B i j) = B := by
  simp [budget, environment, FixedArrayTable.read_ofFn]

@[simp] theorem lower_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) :
    lower.realValue (environment G B i j) = G.lower i j := by
  simp [lower, reflectedP, reflectedQ, OverlapGluing.lower, overlapLower,
    hFirst, hSecond, AffineProbe.coordinate, AffineProbe.reflectedCoordinate]

@[simp] theorem upper_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) :
    upper.realValue (environment G B i j) = G.upper i j := by
  simp [upper, reflectedP, reflectedQ, OverlapGluing.upper, overlapUpper,
    hFirst, hSecond, AffineProbe.coordinate, AffineProbe.reflectedCoordinate]

theorem weight_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) :
    weight.realValue (environment G B i j) = G.weight i j := by
  rw [G.weight_formula]
  simp [weight, absolute_realValue, lower_value G B i j hFirst hSecond,
    upper_value G B i j hFirst hSecond, reflectedP, reflectedQ,
    hFirst, hSecond, AffineProbe.coordinate, AffineProbe.reflectedCoordinate]

theorem curve_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) (z : Expr) (r : Fin 4) :
    (curve z r).realValue (environment G B i j) =
      (G.curve i j).value (z.realValue (environment G B i j)) r := by
  fin_cases r <;> simp [curve, interpolate, firstInverse, secondInverse, reflectedP, reflectedQ,
    OverlapGluing.curve, pairGlueCurve, glueAllocation, SegmentLottery.pointAt, SegmentLottery.point,
    segmentPoint, inverseParameter, hFirst, hSecond, AffineProbe.coordinate, AffineProbe.reflectedCoordinate]

theorem fallback_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) (r : Fin 4) :
    (fallback r).realValue (environment G B i j) = budgetRow B r := by
  fin_cases r <;> simp [fallback, budgetRow]

theorem safeP_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) (r : Fin 4) :
    (safeP r).realValue (environment G B i j) = G.safeP B i j r := by
  simp only [safeP, RationalExpression.realValue_ifLe, weight_value G B i j hFirst hSecond,
    RationalExpression.realValue_literal, Rat.cast_zero, curve_value G B i j hFirst hSecond,
    lower_value G B i j hFirst hSecond, fallback_value, OverlapGluing.safeP]
  by_cases hw : 0 < G.weight i j
  · rw [ite_eq_right (not_le.mpr hw), ite_eq_left hw]
  · rw [ite_eq_left (le_of_not_gt hw), ite_eq_right hw]

theorem safeQ_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) (r : Fin 4) :
    (safeQ r).realValue (environment G B i j) = G.safeQ B i j r := by
  simp only [safeQ, RationalExpression.realValue_ifLe, weight_value G B i j hFirst hSecond,
    RationalExpression.realValue_literal, Rat.cast_zero, curve_value G B i j hFirst hSecond,
    upper_value G B i j hFirst hSecond, fallback_value, OverlapGluing.safeQ]
  by_cases hw : 0 < G.weight i j
  · rw [ite_eq_right (not_le.mpr hw), ite_eq_left hw]
  · rw [ite_eq_left (le_of_not_gt hw), ite_eq_right hw]

end Blotto.RealOverlapFormula
