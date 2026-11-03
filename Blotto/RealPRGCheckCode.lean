import Blotto.RationalPRGCheckCost
import Blotto.RealExpression

/-! Exact-real interpretation of the primary explicit promise checker. The
same conditions are checked, including highest-level normalization and ordered
budgets. Operation labels do not provide floating-point or allocator contracts. -/

namespace Blotto.RealPRGCheckCode
open scoped BigOperators Classical

def Checks {n : ℕ} (values : Fin n → ℝ) (a b : ℝ) : Prop :=
  (∀ j, 0 < values j) ∧ (∑ j, values j) = 1 ∧ 0 < a ∧ 0 < b ∧ b ≤ a ∧ ∀ j, 2 * a * values j ≤ b

noncomputable def checksBool {n : ℕ} (values : Fin n → ℝ) (a b : ℝ) : Bool :=
  let row := List.ofFn values
  row.all (fun q => decide (0 < q)) && decide (row.sum = 1) && decide (0 < a) &&
    decide (0 < b) && decide (b ≤ a) && row.all (fun q => decide (2 * a * q ≤ b))

theorem checksBool_iff {n : ℕ} (values : Fin n → ℝ) (a b : ℝ) :
    checksBool values a b = true ↔ Checks values a b := by
  simp [checksBool, Checks, List.sum_ofFn, List.mem_ofFn, and_assoc]

theorem checks_cast {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) :
    Checks (fun j => (values j : ℝ)) (a : ℝ) (b : ℝ) ↔ RationalPRGChecks values a b := by
  simp only [Checks, RationalPRGChecks]
  norm_cast

theorem checksBool_cast {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) :
    checksBool (fun j => (values j : ℝ)) (a : ℝ) (b : ℝ) = rationalPRGChecksBool values a b := by
  have h := (checksBool_iff (fun j => (values j : ℝ)) (a : ℝ) (b : ℝ)).trans
    ((checks_cast values a b).trans (rationalPRGChecksBool_iff values a b).symm)
  cases hReal : checksBool (fun j => (values j : ℝ)) (a : ℝ) (b : ℝ) <;>
    cases hRat : rationalPRGChecksBool values a b <;> simp_all

noncomputable def fieldEnvironment (a q : ℝ) : FixedArrayTable 2 ℝ := FixedArrayTable.ofFn ![a, q]

theorem field_value (a q : ℝ) :
    RationalPRGCheckCode.fieldExpression.realValue (fieldEnvironment a q) = 2 * a * q := by
  simp [RationalPRGCheckCode.fieldExpression, fieldEnvironment, FixedArrayTable.read_ofFn]

theorem field_operations (a q : ℝ) :
    (RationalPRGCheckCode.fieldExpression.runReal (fieldEnvironment a q)).2 = 5 := rfl

def listSumOperationWork : List ℝ → ℕ
  | [] => 1
  | _ :: rest => listSumOperationWork rest + 4

theorem listSumOperationWork_eq (row : List ℝ) : listSumOperationWork row = 4 * row.length + 1 := by
  induction row with
  | nil => rfl
  | cons q rest ih => simp only [listSumOperationWork, List.length_cons, ih]; omega

noncomputable def operationAllowance {n : ℕ} (values : Fin n → ℝ) (a : ℝ) : ℕ :=
  2 * n + 4 * n + listSumOperationWork (List.ofFn values) + 16 +
    (∑ j, ((RationalPRGCheckCode.fieldExpression.runReal (fieldEnvironment a (values j))).2 + 4)) + 6

theorem operationAllowance_eq {n : ℕ} (values : Fin n → ℝ) (a : ℝ) :
    operationAllowance values a = 19 * n + 23 := by
  simp only [operationAllowance, listSumOperationWork_eq, List.length_ofFn, field_operations]
  simp
  omega

end Blotto.RealPRGCheckCode
