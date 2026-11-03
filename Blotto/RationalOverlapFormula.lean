import Blotto.OverlapFormulaCode
import Blotto.RationalOverlapDescriptor

/-! Rational evaluation of the portable overlap expressions equals the existing
coordinate/reflected-coordinate gluing formulas, including total divisions. -/

namespace Blotto.RationalOverlapFormula
open OverlapFormulaCode

def environment {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ)
    (i : Fin k) (j : Fin h) : FixedArrayTable 16 ℚ :=
  FixedArrayTable.ofFn ![G.first.P i 0, G.first.P i 1, G.first.P i 2,
    G.first.Q i 0, G.first.Q i 1, G.first.Q i 2,
    G.second.P j 0, G.second.P j 1, G.second.P j 2,
    G.second.Q j 0, G.second.Q j 1, G.second.Q j 2,
    G.first.weight i, G.second.weight j, G.d, B]

@[simp] theorem firstP_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) (r : Fin 3) :
    (firstP r).value (environment G B i j) = G.first.P i r := by
  fin_cases r <;> simp [firstP, environment, FixedArrayTable.read_ofFn]
@[simp] theorem firstQ_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) (r : Fin 3) :
    (firstQ r).value (environment G B i j) = G.first.Q i r := by
  fin_cases r <;> simp [firstQ, environment, FixedArrayTable.read_ofFn]
@[simp] theorem secondP_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) (r : Fin 3) :
    (secondP r).value (environment G B i j) = G.second.P j r := by
  fin_cases r <;> simp [secondP, environment, FixedArrayTable.read_ofFn]
@[simp] theorem secondQ_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) (r : Fin 3) :
    (secondQ r).value (environment G B i j) = G.second.Q j r := by
  fin_cases r <;> simp [secondQ, environment, FixedArrayTable.read_ofFn]
@[simp] theorem firstWeight_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    firstWeight.value (environment G B i j) = G.first.weight i := by
  simp [firstWeight, environment, FixedArrayTable.read_ofFn]
@[simp] theorem secondWeight_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    secondWeight.value (environment G B i j) = G.second.weight j := by
  simp [secondWeight, environment, FixedArrayTable.read_ofFn]
@[simp] theorem intervalLength_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    intervalLength.value (environment G B i j) = G.d := by
  simp [intervalLength, environment, FixedArrayTable.read_ofFn]
@[simp] theorem budget_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    budget.value (environment G B i j) = B := by
  simp [budget, environment, FixedArrayTable.read_ofFn]

@[simp] theorem lower_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    lower.value (environment G B i j) = G.lower i j := by
  simp [lower, reflectedP, reflectedQ, RationalOverlapGluing.lower]

@[simp] theorem upper_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    upper.value (environment G B i j) = G.upper i j := by
  simp [upper, reflectedP, reflectedQ, RationalOverlapGluing.upper]

theorem weight_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    weight.value (environment G B i j) = G.weight i j := by
  simp [weight, absolute_value, RationalOverlapGluing.weight, lower_value,
    upper_value, reflectedP, reflectedQ]

theorem curve_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (z : Expr) (r : Fin 4) :
    (curve z r).value (environment G B i j) =
      G.curve i j (z.value (environment G B i j)) r := by
  fin_cases r <;> simp [curve, interpolate, firstInverse, secondInverse, reflectedP, reflectedQ,
    RationalOverlapGluing.curve, rationalSegmentPoint]

theorem fallback_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) (r : Fin 4) :
    (fallback r).value (environment G B i j) = (![B, 0, 0, 0] : Fin 4 → ℚ) r := by
  fin_cases r <;> simp [fallback]

theorem safeP_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (r : Fin 4) :
    (safeP r).value (environment G B i j) = G.safeP B i j r := by
  simp only [safeP, RationalExpression.value_ifLe, weight_value G B i j,
    RationalExpression.value_literal, curve_value G B i j,
    lower_value G B i j, fallback_value, RationalOverlapGluing.safeP]
  by_cases hw : 0 < G.weight i j
  · rw [ite_eq_right (not_le.mpr hw), ite_eq_left hw]
  · rw [ite_eq_left (le_of_not_gt hw), ite_eq_right hw]

theorem safeQ_value {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (r : Fin 4) :
    (safeQ r).value (environment G B i j) = G.safeQ B i j r := by
  simp only [safeQ, RationalExpression.value_ifLe, weight_value G B i j,
    RationalExpression.value_literal, curve_value G B i j,
    upper_value G B i j, fallback_value, RationalOverlapGluing.safeQ]
  by_cases hw : 0 < G.weight i j
  · rw [ite_eq_right (not_le.mpr hw), ite_eq_left hw]
  · rw [ite_eq_left (le_of_not_gt hw), ite_eq_right hw]

end Blotto.RationalOverlapFormula
