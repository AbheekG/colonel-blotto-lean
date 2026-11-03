import Blotto.RationalNestedResidual
import Blotto.RationalNestedFieldHeight

/-! Counted arithmetic for every residual weight and endpoint. This is the
actual three-slot middle-case table, including zero weights. -/

namespace Blotto.RationalNestedResidualCode

abbrev Expr := RationalExpression 5
def U : Expr := .input 0
def V : Expr := .input 1
def W : Expr := .input 2
def H : Expr := .input 3
def T : Expr := .input 4
def A : Expr := .add (.add V W) H
def D : Expr := .add (.add U W) H
def C : Expr := .add (.add U V) H
def G : Expr := .add V H
def S : Expr := .sub U T
def denominator : Expr := .add (.mul G D) (.mul W S)
def weights : Fin 3 → Expr :=
  ![.div (.mul W S) denominator, .div (.mul G (.sub D S)) denominator, .div (.mul G S) denominator]
def vertices : Fin 3 → Fin 3 → Expr :=
  ![![.literal 0, D, V], ![W, .literal 0, C], ![A, S, T]]

def environment (r : RationalNestedResidual) : FixedArrayTable 5 ℚ :=
  FixedArrayTable.ofFn ![r.g.u, r.g.v, r.g.w, r.g.h, r.t]

theorem weight_value (r : RationalNestedResidual) (slot : Fin 3) :
    (weights slot).value (environment r) = r.weight slot := by
  fin_cases slot <;> simp [weights, denominator, G, D, S, U, V, W, H, T, environment,
    FixedArrayTable.read_ofFn, RationalNestedResidual.weight, RationalNestedResidual.K,
    RationalNestedResidual.s, RationalThreeGeometry.G, RationalThreeGeometry.d]

theorem vertex_value (r : RationalNestedResidual) (slot j : Fin 3) :
    (vertices slot j).value (environment r) = r.vertex slot j := by
  fin_cases slot <;> fin_cases j <;> simp [vertices, A, D, C, S, U, V, W, H, T, environment,
    FixedArrayTable.read_ofFn, RationalNestedResidual.vertex, RationalNestedResidual.s,
    RationalThreeGeometry.a, RationalThreeGeometry.d, RationalThreeGeometry.c]

theorem weight_operationBound (slot : Fin 3) : (weights slot).operationBound ≤ 128 := by fin_cases slot <;> decide
theorem weight_depth (slot : Fin 3) : (weights slot).depth ≤ 8 := by fin_cases slot <;> decide
theorem vertex_operationBound (slot j : Fin 3) : (vertices slot j).operationBound ≤ 16 := by fin_cases slot <;> fin_cases j <;> decide
theorem vertex_depth (slot j : Fin 3) : (vertices slot j).depth ≤ 3 := by fin_cases slot <;> fin_cases j <;> decide

theorem weight_literals (slot : Fin 3) : (weights slot).LiteralHeights 2 := by
  fin_cases slot <;> norm_num [weights, denominator, G, D, S, U, V, W, H, T, RationalExpression.LiteralHeights]

theorem vertex_literals (slot j : Fin 3) : (vertices slot j).LiteralHeights 2 := by
  fin_cases slot <;> fin_cases j <;> norm_num [vertices, A, D, C, S, U, V, W, H, T,
    RationalExpression.LiteralHeights, RationalHeight]

theorem weight_height (r : RationalNestedResidual) (slot : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    RationalHeight (r.weight slot) (expressionHeightBudget s 8) := by
  have h := ((weights slot).run_height _ s hEnv ((weights slot).LiteralHeights_mono hs (weight_literals slot))).mono
    (expressionHeightBudget_mono s (weight_depth slot))
  change RationalHeight ((weights slot).value (environment r)) _ at h
  rw [weight_value] at h
  exact h

theorem vertex_height (r : RationalNestedResidual) (slot j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    RationalHeight (r.vertex slot j) (expressionHeightBudget s 3) := by
  have h := ((vertices slot j).run_height _ s hEnv ((vertices slot j).LiteralHeights_mono hs (vertex_literals slot j))).mono
    (expressionHeightBudget_mono s (vertex_depth slot j))
  change RationalHeight ((vertices slot j).value (environment r)) _ at h
  rw [vertex_value] at h
  exact h

theorem weight_operations (r : RationalNestedResidual) (slot : Fin 3) :
    ((weights slot).run (environment r)).2 ≤ 128 :=
  ((weights slot).run_operations_le _).trans (weight_operationBound slot)

theorem weight_intermediates (r : RationalNestedResidual) (slot : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    (weights slot).AllRunHeights (environment r) (expressionHeightBudget s 8) := by
  have h := (weights slot).run_all_heights _ s hEnv ((weights slot).LiteralHeights_mono hs (weight_literals slot))
  exact RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s (weight_depth slot)) h

theorem descriptor_height (r : RationalNestedResidual) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment r).read j) s) :
    r.segmentLottery.HeightAt (expressionHeightBudget s 8) := by
  constructor
  · intro slot; exact weight_height r slot s hs hEnv
  · intro slot j
    have hm := expressionHeightBudget_mono s (by decide : 3 ≤ 8)
    exact ⟨(vertex_height r _ j s hs hEnv).mono hm, (vertex_height r _ j s hs hEnv).mono hm⟩

end Blotto.RationalNestedResidualCode
