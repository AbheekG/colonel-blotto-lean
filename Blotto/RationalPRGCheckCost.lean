import Blotto.RationalPRGRecognition
import Blotto.RationalListSumBitCost
import Blotto.RationalExpressionValue

/-! Primitive/read/write prices for the primary explicit Boolean PRG checks.
The allowance evaluates all stages even if the checker short-circuits. Row
materialization pays its rational words; list/index/backend/ownership costs
are separate. Bounds apply to rejected data without positivity assumptions. -/

namespace Blotto.RationalPRGCheckCode
open scoped BigOperators

def inputWordWidth {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) : ℕ :=
  rationalWordWidth a + rationalWordWidth b + ∑ j, rationalWordWidth (values j)

def fieldExpression : RationalExpression 2 := .mul (.mul (.literal 2) (.input 0)) (.input 1)

def fieldEnvironment (a q : ℚ) : FixedArrayTable 2 ℚ := FixedArrayTable.ofFn ![a, q]

theorem field_value (a q : ℚ) : fieldExpression.value (fieldEnvironment a q) = 2 * a * q := by
  simp [fieldExpression, fieldEnvironment, FixedArrayTable.read_ofFn]

theorem field_operations : fieldExpression.operationBound = 5 := rfl

def comparisonBitCost (model : RationalCostModel) (q r : ℚ) : ℕ :=
  rationalWordWidth q + rationalWordWidth r + model.rat (RationalExpression.pairWidth q r) + 1

theorem comparisonBitCost_bound (model : RationalCostModel) (q r : ℚ) (W : ℕ)
    (hW : 1 ≤ W) (hq : rationalWordWidth q ≤ W) (hr : rationalWordWidth r ≤ W) :
    comparisonBitCost model q r ≤ 4 * model.rat W := by
  have hqP := hq.trans (model.word_le W)
  have hrP := hr.trans (model.word_le W)
  have hCall := model.monotone (max_le hq hr)
  have hOne := hW.trans (model.word_le W)
  unfold comparisonBitCost RationalExpression.pairWidth
  omega

def fieldBitCost (model : RationalCostModel) (a b q : ℚ) : ℕ :=
  fieldExpression.bitCost model (fieldEnvironment a q) + comparisonBitCost model (2 * a * q) b

theorem fieldBitCost_bound (model : RationalCostModel) (a b q : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (ha : RationalHeight a s) (hb : RationalHeight b s) (hq : RationalHeight q s) :
    fieldBitCost model a b q ≤ 9 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hTwo : RationalHeight (2 : ℚ) s := (show RationalHeight (2 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv : ∀ j, RationalHeight ((fieldEnvironment a q).read j) s := by
    intro j
    fin_cases j <;> simp [fieldEnvironment, FixedArrayTable.read_ofFn, ha, hq]
  have hLit : fieldExpression.LiteralHeights s := by simp [fieldExpression, RationalExpression.LiteralHeights, hTwo]
  have hDepth : fieldExpression.depth = 2 := rfl
  have hIntermediates := fieldExpression.run_all_heights (fieldEnvironment a q) s hEnv hLit
  rw [hDepth] at hIntermediates
  have hExpr := fieldExpression.bitCost_bound model (fieldEnvironment a q) _ hIntermediates
  rw [field_operations] at hExpr
  have hOutput := fieldExpression.run_height (fieldEnvironment a q) s hEnv hLit
  rw [hDepth] at hOutput
  change RationalHeight (fieldExpression.value (fieldEnvironment a q)) _ at hOutput
  rw [field_value] at hOutput
  have hBudget := hb.mono (expressionHeightBudget_ge_input s 2)
  have hCompare := comparisonBitCost_bound model (2 * a * q) b _ (by omega)
    (rationalWordWidth_of_height hOutput) (rationalWordWidth_of_height hBudget)
  unfold fieldBitCost
  omega

def recognitionWidth (n s : ℕ) : ℕ :=
  max (1 + 2 * expressionHeightBudget s 2) (1 + 2 * ((s + 1) * n + 1))

def bitAllowance {n : ℕ} (model : RationalCostModel) (values : Fin n → ℚ) (a b : ℚ) : ℕ :=
  let row := List.ofFn values
  2 * (∑ j, rationalWordWidth (values j)) +
    (∑ j, comparisonBitCost model 0 (values j)) + rationalListSumBitCost model row +
      comparisonBitCost model row.sum 1 + comparisonBitCost model 0 a + comparisonBitCost model 0 b +
        comparisonBitCost model b a + (∑ j, fieldBitCost model a b (values j)) + 6

theorem bitAllowance_bound {n : ℕ} (model : RationalCostModel) (values : Fin n → ℚ) (a b : ℚ)
    (s : ℕ) (hs : 2 ≤ s) (ha : RationalHeight a s) (hb : RationalHeight b s)
    (hv : ∀ j, RationalHeight (values j) s) :
    bitAllowance model values a b ≤ (19 * n + 23) * model.rat (recognitionWidth n s) := by
  let W := recognitionWidth n s
  let P := model.rat W
  have hPoint : 1 + 2 * s ≤ W := (Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (expressionHeightBudget_ge_input s 2)) 1).trans (le_max_left _ _)
  have hZero : rationalWordWidth (0 : ℚ) ≤ W := by
    have he : rationalWordWidth (0 : ℚ) = 3 := by decide
    omega
  have hOne : rationalWordWidth (1 : ℚ) ≤ W := by
    have he : rationalWordWidth (1 : ℚ) = 3 := by decide
    omega
  have hAW := (rationalWordWidth_of_height ha).trans hPoint
  have hBW := (rationalWordWidth_of_height hb).trans hPoint
  have hVW := fun j => (rationalWordWidth_of_height (hv j)).trans hPoint
  have hRow : ∀ q ∈ List.ofFn values, RationalHeight q s := by
    intro q hq
    rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩
    exact hv j
  have hRowWidth : 1 + 2 * ((s + 1) * (List.ofFn values).length + 1) ≤ W := by
    simp only [List.length_ofFn]
    exact le_max_right _ _
  have hSum := rationalListSumBitCost_bound model (List.ofFn values) s W hRow hRowWidth
  simp only [List.length_ofFn] at hSum
  have hSumW := (rationalWordWidth_of_height (RationalHeight.list_sum hRow)).trans hRowWidth
  have hNormalize := comparisonBitCost_bound model (List.ofFn values).sum 1 W (by omega) hSumW hOne
  have hA := comparisonBitCost_bound model 0 a W (by omega) hZero hAW
  have hB := comparisonBitCost_bound model 0 b W (by omega) hZero hBW
  have hOrder := comparisonBitCost_bound model b a W (by omega) hBW hAW
  have hValues : (∑ j, rationalWordWidth (values j)) ≤ n * P := by
    calc
      _ ≤ ∑ _j : Fin n, P := Finset.sum_le_sum (fun j _ => (hVW j).trans (model.word_le W))
      _ = _ := by simp
  have hPositive : (∑ j, comparisonBitCost model 0 (values j)) ≤ 4 * n * P := by
    calc
      _ ≤ ∑ _j : Fin n, 4 * P := Finset.sum_le_sum (fun j _ => comparisonBitCost_bound model 0 (values j) W (by omega) hZero (hVW j))
      _ = _ := by simp; ring
  have hFields : (∑ j, fieldBitCost model a b (values j)) ≤ 9 * n * P := by
    calc
      _ ≤ ∑ _j : Fin n, 9 * P := Finset.sum_le_sum (fun j _ =>
        (fieldBitCost_bound model a b (values j) s hs ha hb (hv j)).trans
          (Nat.mul_le_mul_left _ (model.monotone (le_max_left _ _))))
      _ = _ := by simp; ring
  have hControl : 6 ≤ 6 * P := by have hP : 1 ≤ P := (by omega : 1 ≤ W).trans (model.word_le W); omega
  change rationalListSumBitCost model (List.ofFn values) ≤ (4 * n + 1) * P at hSum
  change comparisonBitCost model (List.ofFn values).sum 1 ≤ 4 * P at hNormalize
  change comparisonBitCost model 0 a ≤ 4 * P at hA
  change comparisonBitCost model 0 b ≤ 4 * P at hB
  change comparisonBitCost model b a ≤ 4 * P at hOrder
  change bitAllowance model values a b ≤ (19 * n + 23) * P
  unfold bitAllowance
  nlinarith

theorem original_input_heights {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) :
    RationalHeight a (3 + inputWordWidth values a b) ∧ RationalHeight b (3 + inputWordWidth values a b) ∧
      ∀ j, RationalHeight (values j) (3 + inputWordWidth values a b) := by
  have hA : rationalWordWidth a ≤ 3 + inputWordWidth values a b := by unfold inputWordWidth; omega
  have hB : rationalWordWidth b ≤ 3 + inputWordWidth values a b := by unfold inputWordWidth; omega
  refine ⟨(rationalHeight_of_wordWidth a).mono hA, (rationalHeight_of_wordWidth b).mono hB, ?_⟩
  intro j
  have hV := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun k => rationalWordWidth (values k)) (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
  exact (rationalHeight_of_wordWidth (values j)).mono (by unfold inputWordWidth; omega)

theorem bitAllowance_original_bound {n : ℕ} (model : RationalCostModel) (values : Fin n → ℚ) (a b : ℚ) :
    bitAllowance model values a b ≤
      (19 * n + 23) * model.rat (recognitionWidth n (3 + inputWordWidth values a b)) := by
  have h := original_input_heights values a b
  exact bitAllowance_bound model values a b _ (by omega) h.1 h.2.1 h.2.2

end Blotto.RationalPRGCheckCode
