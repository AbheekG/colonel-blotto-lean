import Blotto.RationalFirstMidpointPreparation

/-! Fixed-mean family inputs price the actual probability formula and six
stored parameter words before the first-case midpoint table. One invocation
is covered; caller/factory multiplicities and backend costs remain separate. -/

namespace Blotto.RationalNestedInput
open scoped BigOperators

def familyInputFields (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) : Fin 6 → ℚ :=
  let j := i.familyInput x hx0 hxv
  ![j.M, j.a, j.d, j.c, j.t, j.q]

theorem FieldsHeight.familyInputFields {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (hX : RationalHeight x s) :
    ∀ j, RationalHeight (i.familyInputFields x hx0 hxv j) (expressionHeightBudget s 8) := by
  have hp := h.familyInput hs x hx0 hxv hX
  intro j
  fin_cases j
  · change RationalHeight (i.familyInput x hx0 hxv).M _
    exact hp.1
  · change RationalHeight (i.familyInput x hx0 hxv).a _
    exact hp.2.1
  · change RationalHeight (i.familyInput x hx0 hxv).d _
    exact hp.2.2.1
  · change RationalHeight (i.familyInput x hx0 hxv).c _
    exact hp.2.2.2.1
  · change RationalHeight (i.familyInput x hx0 hxv).t _
    exact hp.2.2.2.2.1
  · change RationalHeight (i.familyInput x hx0 hxv).q _
    exact hp.2.2.2.2.2

def familyInputBitCost (model : RationalCostModel) (i : RationalNestedInput)
    (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) : ℕ :=
  (RationalNestedParametersCode.scalarPrograms 2).bitCost model (RationalNestedParametersCode.environment i x) +
    ∑ j : Fin 6, rationalWordWidth (i.familyInputFields x hx0 hxv j)

theorem FieldsHeight.familyInputBitCost_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (hX : RationalHeight x s) :
    i.familyInputBitCost model x hx0 hxv ≤ 134 * model.rat (1 + 2 * expressionHeightBudget s 8) := by
  have hc := RationalNestedParametersCode.scalar_bitCost model i x 2 s hs (h.environment x hX)
  have hp : (∑ j : Fin 6, rationalWordWidth (i.familyInputFields x hx0 hxv j)) ≤
      6 * model.rat (1 + 2 * expressionHeightBudget s 8) := by
    calc
      _ ≤ ∑ _j : Fin 6, model.rat (1 + 2 * expressionHeightBudget s 8) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (h.familyInputFields hs x hx0 hxv hX j)).trans (model.word_le _))
      _ = _ := by simp
  unfold familyInputBitCost
  omega

noncomputable def familyMidpointPreparedBitCost (model : RationalCostModel) (primitive : ℕ → ℕ)
    (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) (outerBits : Fin K → Bool) : ℕ :=
  i.familyInputBitCost model x hx0 hxv +
    (i.familyInput x hx0 hxv).firstMidpointPreparedBitCost model primitive hxv K outerBits

theorem FieldsHeight.familyMidpointPreparedBitCost_bound {i : RationalNestedInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v)
    (hX : RationalHeight x s) (K : ℕ) (outerBits : Fin K → Bool) :
    i.familyMidpointPreparedBitCost model primitive x hx0 hxv K outerBits ≤
      134 * model.rat (1 + 2 * expressionHeightBudget s 8) +
        (3 * K + (4 + 2 * c) * K * binaryWordWidth K + c * (K + 2) +
          11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
            136 * model.rat (1 + 2 * expressionHeightBudget (max (expressionHeightBudget s 8) (K + 2)) 8) +
              3052 * model.rat (1 + 2 * expressionHeightBudget (max (expressionHeightBudget s 8) (K + 2)) 28)) := by
  have hf := h.familyInputBitCost_bound hs model x hx0 hxv hX
  have hp := (h.familyInput hs x hx0 hxv hX).firstMidpointPreparedBitCost_bound
    (hs.trans (expressionHeightBudget_ge_input s 8)) model primitive c hPrimitive hxv K outerBits
  unfold familyMidpointPreparedBitCost
  omega

end Blotto.RationalNestedInput
