import Blotto.RationalAffineHeight
import Blotto.RationalExpressionBitCost
import Blotto.PreparedSegmentDescriptorHeight

/-! Dense merge/split rows retain all products and the actual positive pair
denominator. Sparse coefficients bound every intermediate at three levels.
Child-table production, indices/backend/ownership are separate. -/

namespace Blotto.RationalSplitCode
open scoped BigOperators

abbrev Expr := RationalExpression 5
def denominator : Expr := .add (.input 0) (.input 1)
def firstCoefficient (j : Fin 4) : Expr :=
  if j = 0 then .div (.input 0) denominator else if j = 1 then .div (.input 1) denominator else .literal 0
def row (j : Fin 4) : Expr :=
  .add (.add (.add (.add (.literal 0) (.mul (firstCoefficient j) (.input 2)))
    (.mul (.literal (if j = 2 then 1 else 0)) (.input 3)))
      (.mul (.literal (if j = 3 then 1 else 0)) (.input 4))) (.literal 0)
def environment (a d : ℚ) (x : Fin 3 → ℚ) : FixedArrayTable 5 ℚ := FixedArrayTable.ofFn ![a, d, x 0, x 1, x 2]

theorem row_value (a d : ℚ) (x : Fin 3 → ℚ) (j : Fin 4) :
    (row j).value (environment a d x) = (RationalAffineAllocation.splitFirstTwo a d).value x j := by
  rw [RationalAffineAllocation.splitFirstTwo_value]
  fin_cases j <;> simp [row, firstCoefficient, denominator, environment, FixedArrayTable.read_ofFn]

theorem row_operations (j : Fin 4) : (row j).operationBound ≤ 20 := by fin_cases j <;> decide

theorem row_intermediates (a d : ℚ) (x : Fin 3 → ℚ) (j : Fin 4) (s : ℕ) (hs : 2 ≤ s)
    (ha : 0 < a) (hd : 0 < d) (hA : RationalHeight a s) (hD : RationalHeight d s)
    (hX : ∀ k, RationalHeight (x k) s) :
    (row j).AllRunHeights (environment a d x) (expressionHeightBudget s 3) := by
  have hDen : a + d ≠ 0 := ne_of_gt (add_pos ha hd)
  have hA0 : RationalHeight a (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hA
  have hD0 : RationalHeight d (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hD
  have hSum := hA0.add_level hD0
  have hm1 := expressionHeightBudget_ge_input s 1
  have hm2 := expressionHeightBudget_ge_input s 2
  have hQA := (hA.mono hm1).div_level hSum
  have hQD := (hD.mono hm1).div_level hSum
  have hPA := hQA.mul_level ((hX 0).mono hm2)
  have hPD := hQD.mul_level ((hX 0).mono hm2)
  have hSum3 := hSum.mono (expressionHeightBudget_mono s (by decide : 1 ≤ 3))
  have hQA3 := hQA.mono (expressionHeightBudget_mono s (by decide : 2 ≤ 3))
  have hQD3 := hQD.mono (expressionHeightBudget_mono s (by decide : 2 ≤ 3))
  have hA3 := hA.mono (expressionHeightBudget_ge_input s 3)
  have hD3 := hD.mono (expressionHeightBudget_ge_input s 3)
  have hX3 := fun k => (hX k).mono (expressionHeightBudget_ge_input s 3)
  have hZero : RationalHeight (0 : ℚ) (expressionHeightBudget s 3) :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 3))
  have hOne : RationalHeight (1 : ℚ) (expressionHeightBudget s 3) :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 3))
  fin_cases j <;> simp [row, firstCoefficient, denominator, environment, FixedArrayTable.read_ofFn,
    RationalExpression.AllRunHeights, RationalExpression.run, hDen, hA3, hD3, hX3, hZero, hOne,
    hSum3, hQA3, hQD3, hPA, hPD]

theorem row_bitCost (model : RationalCostModel) (a d : ℚ) (x : Fin 3 → ℚ) (j : Fin 4) (s : ℕ) (hs : 2 ≤ s)
    (ha : 0 < a) (hd : 0 < d) (hA : RationalHeight a s) (hD : RationalHeight d s) (hX : ∀ k, RationalHeight (x k) s) :
    (row j).bitCost model (environment a d x) ≤ 20 * model.rat (1 + 2 * expressionHeightBudget s 3) :=
  ((row j).bitCost_bound model _ _ (row_intermediates a d x j s hs ha hd hA hD hX)).trans
    (Nat.mul_le_mul_right _ (row_operations j))

def descriptorFormulaBitCost (model : RationalCostModel) (a d : ℚ) (l : RationalSegmentLottery 3 9) : ℕ :=
  (∑ slot : Fin 9, ∑ j : Fin 4, (row j).bitCost model (environment a d (l.P slot))) +
    ∑ slot : Fin 9, ∑ j : Fin 4, (row j).bitCost model (environment a d (l.Q slot))

theorem descriptorFormulaBitCost_bound (model : RationalCostModel) (a d : ℚ) (l : RationalSegmentLottery 3 9)
    (s : ℕ) (hs : 2 ≤ s) (ha : 0 < a) (hd : 0 < d) (hA : RationalHeight a s) (hD : RationalHeight d s) (h : l.HeightAt s) :
    descriptorFormulaBitCost model a d l ≤ 1440 * model.rat (1 + 2 * expressionHeightBudget s 3) := by
  have hP : (∑ slot : Fin 9, ∑ j : Fin 4, (row j).bitCost model (environment a d (l.P slot))) ≤
      9 * (4 * (20 * model.rat (1 + 2 * expressionHeightBudget s 3))) := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 4, 20 * model.rat (1 + 2 * expressionHeightBudget s 3) := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => row_bitCost model a d _ j s hs ha hd hA hD (fun k => (h.2 slot k).1)))
      _ = _ := by simp
  have hQ : (∑ slot : Fin 9, ∑ j : Fin 4, (row j).bitCost model (environment a d (l.Q slot))) ≤
      9 * (4 * (20 * model.rat (1 + 2 * expressionHeightBudget s 3))) := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 4, 20 * model.rat (1 + 2 * expressionHeightBudget s 3) := Finset.sum_le_sum (fun slot _ =>
        Finset.sum_le_sum (fun j _ => row_bitCost model a d _ j s hs ha hd hA hD (fun k => (h.2 slot k).2)))
      _ = _ := by simp
  unfold descriptorFormulaBitCost
  nlinarith

def preparedDescriptorBitCost (model : RationalCostModel) (a d : ℚ) (l : RationalSegmentLottery 3 9) : ℕ :=
  descriptorFormulaBitCost model a d l +
    (PreparedSegmentDescriptor.prepare (l.mapped (RationalAffineAllocation.splitFirstTwo a d))).payloadBitCost

theorem preparedDescriptorBitCost_bound (model : RationalCostModel) (a d : ℚ) (l : RationalSegmentLottery 3 9)
    (s : ℕ) (hs : 2 ≤ s) (ha : 0 < a) (hd : 0 < d) (hA : RationalHeight a s) (hD : RationalHeight d s) (h : l.HeightAt s) :
    preparedDescriptorBitCost model a d l ≤ 1521 * model.rat (1 + 2 * expressionHeightBudget s 3) := by
  have hf := descriptorFormulaBitCost_bound model a d l s hs ha hd hA hD h
  have hp := (PreparedSegmentDescriptor.prepare (l.mapped (RationalAffineAllocation.splitFirstTwo a d))).payloadBitCost_bound _
    (h.mapped_split a d hA hD)
  have hw := hp.trans (Nat.mul_le_mul_left 81 (model.word_le _))
  unfold preparedDescriptorBitCost
  omega

end Blotto.RationalSplitCode
