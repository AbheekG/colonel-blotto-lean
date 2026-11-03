import Blotto.RationalExpressionBitCost
import Blotto.RationalHeightBudget
import Blotto.PreparedSegmentDescriptorHeight

/-! Materializing binary/padded descriptors prices every field. Right-branch
complements are recomputed per weight, as in the native definition. Child-table
production, indices/tags, allocation and physical backend remain separate. -/

namespace Blotto.RationalLotteryAssemblyCode
open scoped BigOperators

abbrev Expr := RationalExpression 2
def product : Expr := .mul (.input 0) (.input 1)
def complementProduct : Expr := .mul (.sub (.literal 1) (.input 0)) (.input 1)
def environment (p q : ℚ) : FixedArrayTable 2 ℚ := FixedArrayTable.ofFn ![p, q]

theorem product_value (p q : ℚ) : product.value (environment p q) = p * q := by
  simp [product, environment, FixedArrayTable.read_ofFn]

theorem complementProduct_value (p q : ℚ) : complementProduct.value (environment p q) = (1 - p) * q := by
  simp [complementProduct, environment, FixedArrayTable.read_ofFn]

theorem environment_height {p q : ℚ} {s : ℕ} (hp : RationalHeight p s) (hq : RationalHeight q s) :
    ∀ j, RationalHeight ((environment p q).read j) s := by
  intro j
  fin_cases j
  · simpa [environment, FixedArrayTable.read_ofFn] using hp
  · simpa [environment, FixedArrayTable.read_ofFn] using hq

theorem product_bitCost (model : RationalCostModel) (p q : ℚ) (s : ℕ) (_hs : 2 ≤ s)
    (hp : RationalHeight p s) (hq : RationalHeight q s) :
    product.bitCost model (environment p q) ≤ 3 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hLit : product.LiteralHeights s := by simp [product, RationalExpression.LiteralHeights]
  have h := product.run_all_heights _ s (environment_height hp hq) hLit
  have hm : product.depth ≤ 2 := by decide
  have hb := product.bitCost_bound model _ _ (RationalExpression.AllRunHeights_mono _ _ (expressionHeightBudget_mono s hm) h)
  have ho : product.operationBound = 3 := by decide
  simpa only [ho] using hb

theorem complementProduct_bitCost (model : RationalCostModel) (p q : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hp : RationalHeight p s) (hq : RationalHeight q s) :
    complementProduct.bitCost model (environment p q) ≤ 5 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hLit : complementProduct.LiteralHeights s := by simpa [complementProduct, RationalExpression.LiteralHeights] using hOne
  have h := complementProduct.run_all_heights _ s (environment_height hp hq) hLit
  have hd : complementProduct.depth = 2 := by decide
  rw [hd] at h
  have hb := complementProduct.bitCost_bound model _ _ h
  have ho : complementProduct.operationBound = 5 := by decide
  simpa only [ho] using hb

end Blotto.RationalLotteryAssemblyCode
namespace Blotto.RationalSegmentLottery
open scoped BigOperators

def binaryFormulaBitCost {n k m : ℕ} (model : RationalCostModel) (p : ℚ)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) : ℕ :=
  (∑ slot : Fin k, RationalLotteryAssemblyCode.product.bitCost model
    (RationalLotteryAssemblyCode.environment p (l.weight slot))) +
      ∑ slot : Fin m, RationalLotteryAssemblyCode.complementProduct.bitCost model
        (RationalLotteryAssemblyCode.environment p (t.weight slot))

theorem binaryFormulaBitCost_bound {n k m : ℕ} (model : RationalCostModel) (p : ℚ)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) (s : ℕ) (hs : 2 ≤ s)
    (hp : RationalHeight p s) (hl : l.HeightAt s) (ht : t.HeightAt s) :
    binaryFormulaBitCost model p l t ≤ (3 * k + 5 * m) * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hL : (∑ slot : Fin k, RationalLotteryAssemblyCode.product.bitCost model
      (RationalLotteryAssemblyCode.environment p (l.weight slot))) ≤ k * (3 * model.rat (1 + 2 * expressionHeightBudget s 2)) := by
    calc
      _ ≤ ∑ _slot : Fin k, 3 * model.rat (1 + 2 * expressionHeightBudget s 2) :=
        Finset.sum_le_sum (fun slot _ => RationalLotteryAssemblyCode.product_bitCost model p _ s hs hp (hl.1 slot))
      _ = _ := by simp
  have hR : (∑ slot : Fin m, RationalLotteryAssemblyCode.complementProduct.bitCost model
      (RationalLotteryAssemblyCode.environment p (t.weight slot))) ≤ m * (5 * model.rat (1 + 2 * expressionHeightBudget s 2)) := by
    calc
      _ ≤ ∑ _slot : Fin m, 5 * model.rat (1 + 2 * expressionHeightBudget s 2) :=
        Finset.sum_le_sum (fun slot _ => RationalLotteryAssemblyCode.complementProduct_bitCost model p _ s hs hp (ht.1 slot))
      _ = _ := by simp
  unfold binaryFormulaBitCost
  nlinarith

def binaryPreparedBitCost {n k m : ℕ} (model : RationalCostModel) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) : ℕ :=
  binaryFormulaBitCost model p l t + (PreparedSegmentDescriptor.prepare (binary p hp l t)).payloadBitCost

theorem binaryPreparedBitCost_bound {n k m : ℕ} (model : RationalCostModel) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) (s : ℕ) (hs : 2 ≤ s)
    (hP : RationalHeight p s) (hl : l.HeightAt s) (ht : t.HeightAt s) :
    binaryPreparedBitCost model p hp l t ≤
      (4 * k + 6 * m + 2 * (k + m) * n) * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hf := binaryFormulaBitCost_bound model p l t s hs hP hl ht
  have hp := (PreparedSegmentDescriptor.prepare (binary p hp l t)).payloadBitCost_bound _ (hl.binary ht hs p hp hP)
  have hc := hp.trans (Nat.mul_le_mul_left (k + m + 2 * (k + m) * n) (model.word_le _))
  unfold binaryPreparedBitCost
  nlinarith

def paddingBitCost {n k : ℕ} (l : RationalSegmentLottery n k) (m : ℕ) (fallback : Fin k) : ℕ :=
  (PreparedSegmentDescriptor.prepare (l.padRight m fallback)).payloadBitCost

theorem paddingBitCost_bound {n k : ℕ} (model : RationalCostModel) (l : RationalSegmentLottery n k)
    (m : ℕ) (fallback : Fin k) (s : ℕ) (hs : 2 ≤ s) (h : l.HeightAt s) :
    l.paddingBitCost m fallback ≤ (k + m + 2 * (k + m) * n) * model.rat (1 + 2 * s) :=
  ((PreparedSegmentDescriptor.prepare (l.padRight m fallback)).payloadBitCost_bound s (h.padRight hs m fallback)).trans
    (Nat.mul_le_mul_left _ (model.word_le _))

end Blotto.RationalSegmentLottery
