import Blotto.RationalThreeGeometryCompiler
import Blotto.RationalThreeInput

/-! Original three-variable inputs feed the counted geometry code through
five stored rational words. The exceptional branch remains separate. -/

namespace Blotto.RationalThreeInputCode

abbrev Expr := RationalExpression 5

def B : Expr := .input 0
def A : Expr := .input 1
def D : Expr := .input 2
def C : Expr := .input 3
def P : Expr := .input 4

def parameters : Fin 4 → Expr :=
  ![.sub B A, .sub B D, .sub B C, .mul C (.sub (.literal 1) P)]

def environment (i : RationalThreeInput) : FixedArrayTable 5 ℚ := FixedArrayTable.ofFn ![i.B, i.a, i.d, i.c, i.p]

theorem parameter_value (i : RationalThreeInput) (hE : 0 < i.a + i.d - i.B) (j : Fin 4) :
    (parameters j).value (environment i) = (RationalThreeGeometryCode.environment (i.geometry hE)).read j := by
  fin_cases j <;> simp [parameters, B, A, D, C, P, environment,
    RationalThreeGeometryCode.environment, RationalThreeInput.geometry, FixedArrayTable.read_ofFn]

theorem parameter_operations (j : Fin 4) : (parameters j).operationBound ≤ 8 := by fin_cases j <;> decide

theorem parameter_depth (j : Fin 4) : (parameters j).depth ≤ 2 := by fin_cases j <;> decide

theorem parameter_literals (j : Fin 4) : (parameters j).LiteralHeights 2 := by
  fin_cases j <;> norm_num [parameters, B, A, D, C, P, RationalExpression.LiteralHeights, RationalHeight]

theorem geometry_environment_height (i : RationalThreeInput) (hE : 0 < i.a + i.d - i.B)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    ∀ j, RationalHeight ((RationalThreeGeometryCode.environment (i.geometry hE)).read j) (expressionHeightBudget s 2) := by
  intro j
  have h := (parameters j).run_height (environment i) s hEnv ((parameters j).LiteralHeights_mono hs (parameter_literals j))
  have hm := h.mono (expressionHeightBudget_mono s (parameter_depth j))
  change RationalHeight ((parameters j).value (environment i)) (expressionHeightBudget s 2) at hm
  rw [parameter_value] at hm
  exact hm

theorem chosen_height (i : RationalThreeInput) (hE : 0 < i.a + i.d - i.B) (slot : Fin 9)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    RationalHeight ((i.geometry hE).chosenWeights slot) (expressionHeightBudget (expressionHeightBudget s 2) 16) := by
  have hp : 2 ≤ expressionHeightBudget s 2 := by simp only [expressionHeightBudget]; omega
  exact RationalThreeGeometryCode.chosen_height _ slot _ hp (geometry_environment_height i hE s hs hEnv)

end Blotto.RationalThreeInputCode
