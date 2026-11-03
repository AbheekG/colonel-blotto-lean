import Blotto.RationalLotteryAssemblyBitCost

/-! Third-coordinate translation prices both endpoint additions per slot
and all written fields. The available child descriptor is not recomputed by
this component; its production and caller multiplicities remain separate. -/

namespace Blotto.RationalLotteryAssemblyCode

def sum : Expr := .add (.input 0) (.input 1)

theorem sum_value (p q : ℚ) : sum.value (environment p q) = p + q := by
  simp [sum, environment, FixedArrayTable.read_ofFn]

theorem sum_bitCost (model : RationalCostModel) (p q : ℚ) (s : ℕ)
    (hp : RationalHeight p s) (hq : RationalHeight q s) :
    sum.bitCost model (environment p q) ≤ 3 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hLit : sum.LiteralHeights s := by simp [sum, RationalExpression.LiteralHeights]
  have hAll := sum.run_all_heights _ s (environment_height hp hq) hLit
  have hd : sum.depth = 1 := by decide
  rw [hd] at hAll
  have h := sum.bitCost_bound model _ _ hAll
  have ho : sum.operationBound = 3 := by decide
  simpa only [ho] using h

end Blotto.RationalLotteryAssemblyCode
namespace Blotto.RationalSegmentLottery
open scoped BigOperators

def shiftThirdFormulaBitCost {k : ℕ} (model : RationalCostModel) (l : RationalSegmentLottery 3 k) (x : ℚ) : ℕ :=
  (∑ slot : Fin k, RationalLotteryAssemblyCode.sum.bitCost model
    (RationalLotteryAssemblyCode.environment (l.P slot 2) x)) +
      ∑ slot : Fin k, RationalLotteryAssemblyCode.sum.bitCost model
        (RationalLotteryAssemblyCode.environment (l.Q slot 2) x)

theorem shiftThirdFormulaBitCost_bound {k : ℕ} (model : RationalCostModel) (l : RationalSegmentLottery 3 k)
    (x : ℚ) (s : ℕ) (h : l.HeightAt s) (hx : RationalHeight x s) :
    shiftThirdFormulaBitCost model l x ≤ 6 * k * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hP : (∑ slot : Fin k, RationalLotteryAssemblyCode.sum.bitCost model
      (RationalLotteryAssemblyCode.environment (l.P slot 2) x)) ≤ k * (3 * model.rat (1 + 2 * expressionHeightBudget s 1)) := by
    calc
      _ ≤ ∑ _slot : Fin k, 3 * model.rat (1 + 2 * expressionHeightBudget s 1) := Finset.sum_le_sum (fun slot _ =>
        RationalLotteryAssemblyCode.sum_bitCost model _ x s (h.2 slot 2).1 hx)
      _ = _ := by simp
  have hQ : (∑ slot : Fin k, RationalLotteryAssemblyCode.sum.bitCost model
      (RationalLotteryAssemblyCode.environment (l.Q slot 2) x)) ≤ k * (3 * model.rat (1 + 2 * expressionHeightBudget s 1)) := by
    calc
      _ ≤ ∑ _slot : Fin k, 3 * model.rat (1 + 2 * expressionHeightBudget s 1) := Finset.sum_le_sum (fun slot _ =>
        RationalLotteryAssemblyCode.sum_bitCost model _ x s (h.2 slot 2).2 hx)
      _ = _ := by simp
  unfold shiftThirdFormulaBitCost
  nlinarith

def shiftThirdPreparedBitCost {k : ℕ} (model : RationalCostModel) (l : RationalSegmentLottery 3 k) (x : ℚ) : ℕ :=
  shiftThirdFormulaBitCost model l x + (PreparedSegmentDescriptor.prepare (l.shiftThird x)).payloadBitCost

theorem shiftThirdPreparedBitCost_bound {k : ℕ} (model : RationalCostModel) (l : RationalSegmentLottery 3 k)
    (x : ℚ) (s : ℕ) (h : l.HeightAt s) (hx : RationalHeight x s) :
    shiftThirdPreparedBitCost model l x ≤ 13 * k * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hf := shiftThirdFormulaBitCost_bound model l x s h hx
  have hp := (PreparedSegmentDescriptor.prepare (l.shiftThird x)).payloadBitCost_bound _ (h.shiftThird x hx)
  have hc := hp.trans (Nat.mul_le_mul_left (k + 2 * k * 3) (model.word_le _))
  unfold shiftThirdPreparedBitCost
  nlinarith

end Blotto.RationalSegmentLottery
