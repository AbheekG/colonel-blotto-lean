import Blotto.RationalNestedResidualBitCost
import Blotto.RationalNestedProfileHeight
import Blotto.RationalLotteryAssemblyBitCost

/-! The actual residual input derives its five numerical fields from the
nested parameters. One construction plus its descriptor and optional padding
is priced here; caller multiplicities and metadata/backend remain separate. -/

namespace Blotto.RationalNestedResidualPreparationCode
open RationalNestedParametersCode
open scoped BigOperators

def programs : Fin 5 → RationalNestedParametersCode.Expr := ![U, V, .sub M C, H, T]

theorem field_value (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (j : Fin 5) :
    (programs j).value (RationalNestedParametersCode.environment i 0) =
      (RationalNestedResidualCode.environment (i.residualInput hvt htu)).read j := by
  fin_cases j <;> simp [programs, RationalNestedResidualCode.environment, FixedArrayTable.read_ofFn,
    RationalNestedInput.residualInput, RationalNestedInput.geometry]

theorem operations (j : Fin 5) : (programs j).operationBound ≤ 16 := by fin_cases j <;> decide

theorem depth (j : Fin 5) : (programs j).depth ≤ 2 := by fin_cases j <;> decide

theorem literals (j : Fin 5) (s : ℕ) : (programs j).LiteralHeights s := by
  fin_cases j <;> simp [programs, U, V, H, M, A, D, C, T, Q, RationalExpression.LiteralHeights]

def fieldBitCost (model : RationalCostModel) (i : RationalNestedInput) : ℕ :=
  ∑ j : Fin 5, ((programs j).bitCost model (RationalNestedParametersCode.environment i 0) +
    rationalWordWidth ((programs j).value (RationalNestedParametersCode.environment i 0)))

theorem fieldBitCost_bound (model : RationalCostModel) (i : RationalNestedInput) (s : ℕ)
    (hEnv : ∀ j, RationalHeight ((RationalNestedParametersCode.environment i 0).read j) s) :
    fieldBitCost model i ≤ 85 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hField : ∀ j : Fin 5,
      (programs j).bitCost model (RationalNestedParametersCode.environment i 0) +
        rationalWordWidth ((programs j).value (RationalNestedParametersCode.environment i 0)) ≤
          17 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
    intro j
    have hm := expressionHeightBudget_mono s (depth j)
    have hAll := (programs j).run_all_heights _ s hEnv (literals j s)
    have hc := ((programs j).bitCost_bound model _ _ (RationalExpression.AllRunHeights_mono _ _ hm hAll)).trans
      (Nat.mul_le_mul_right _ (operations j))
    have hv := ((programs j).run_height _ s hEnv (literals j s)).mono hm
    change RationalHeight ((programs j).value (RationalNestedParametersCode.environment i 0)) (expressionHeightBudget s 2) at hv
    have hw := (rationalWordWidth_of_height hv).trans (model.word_le _)
    omega
  calc
    _ ≤ ∑ _j : Fin 5, 17 * model.rat (1 + 2 * expressionHeightBudget s 2) := Finset.sum_le_sum (fun j _ => hField j)
    _ = _ := by simp; ring

end Blotto.RationalNestedResidualPreparationCode
namespace Blotto.RationalNestedInput

theorem FieldsHeight.residualEnvironment {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hvt : i.v < i.t) (htu : i.t < i.u) :
    ∀ j, RationalHeight ((RationalNestedResidualCode.environment (i.residualInput hvt htu)).read j)
      (expressionHeightBudget s 2) := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hEnv := h.environment 0 hZero
  intro j
  rw [← RationalNestedResidualPreparationCode.field_value i hvt htu j]
  have hv := (RationalNestedResidualPreparationCode.programs j).run_height _ s hEnv
    (RationalNestedResidualPreparationCode.literals j s)
  exact hv.mono (expressionHeightBudget_mono s (RationalNestedResidualPreparationCode.depth j))

def residualPreparedBitCost (model : RationalCostModel) (i : RationalNestedInput)
    (hvt : i.v < i.t) (htu : i.t < i.u) : ℕ :=
  RationalNestedResidualPreparationCode.fieldBitCost model i +
    RationalNestedResidualCode.preparedDescriptorBitCost model (i.residualInput hvt htu)

theorem FieldsHeight.residualPreparedBitCost_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (hvt : i.v < i.t) (htu : i.t < i.u) :
    i.residualPreparedBitCost model hvt htu ≤ 778 * model.rat (1 + 2 * expressionHeightBudget s 10) := by
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hf := (RationalNestedResidualPreparationCode.fieldBitCost_bound model i s (h.environment 0 hZero)).trans
    (Nat.mul_le_mul_left 85 (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (expressionHeightBudget_mono s (by decide : 2 ≤ 10))) 1)))
  have hp := RationalNestedResidualCode.preparedDescriptorBitCost_bound model (i.residualInput hvt htu) _
    (hs.trans (expressionHeightBudget_ge_input s 2)) (h.residualEnvironment hs hvt htu)
  rw [expressionHeightBudget_comp] at hp
  change RationalNestedResidualCode.preparedDescriptorBitCost model (i.residualInput hvt htu) ≤
    693 * model.rat (1 + 2 * expressionHeightBudget s 10) at hp
  unfold residualPreparedBitCost
  omega

def paddedResidualPreparedBitCost (model : RationalCostModel) (i : RationalNestedInput)
    (hvt : i.v < i.t) (htu : i.t < i.u) : ℕ :=
  i.residualPreparedBitCost model hvt htu + (i.residualInput hvt htu).segmentLottery.paddingBitCost 6 0

theorem FieldsHeight.paddedResidualPreparedBitCost_bound {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (model : RationalCostModel) (hvt : i.v < i.t) (htu : i.t < i.u) :
    i.paddedResidualPreparedBitCost model hvt htu ≤ 841 * model.rat (1 + 2 * expressionHeightBudget s 10) := by
  have hf := h.residualPreparedBitCost_bound hs model hvt htu
  have hp := (i.residualInput hvt htu).segmentLottery.paddingBitCost_bound model 6 0 _
    (hs.trans (expressionHeightBudget_ge_input s 10)) (h.residual hs hvt htu)
  change (i.residualInput hvt htu).segmentLottery.paddingBitCost 6 0 ≤
    63 * model.rat (1 + 2 * expressionHeightBudget s 10) at hp
  unfold paddedResidualPreparedBitCost
  omega

end Blotto.RationalNestedInput
