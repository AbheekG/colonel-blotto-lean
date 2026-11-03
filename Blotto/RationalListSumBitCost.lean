import Blotto.RationalHeightSum
import Blotto.RationalExpressionBitCost
import Blotto.RationalCategoricalHeight

/-! Rational list-sum prices follow the native right-associated sum, including
operand/result copies. Every suffix sum is bounded; zero/cancellation are allowed.
List traversal, addressing, allocation and the arithmetic backend are separate. -/

namespace Blotto

def rationalListSumBitCost (model : RationalCostModel) : List ℚ → ℕ
  | [] => rationalWordWidth (0 : ℚ)
  | q :: rest => rationalListSumBitCost model rest + rationalWordWidth q + rationalWordWidth rest.sum +
      model.rat (RationalExpression.pairWidth q rest.sum) + rationalWordWidth (q + rest.sum)

theorem rationalListSumBitCost_bound (model : RationalCostModel) (l : List ℚ) (s W : ℕ)
    (hItems : ∀ q ∈ l, RationalHeight q s) (hW : 1 + 2 * ((s + 1) * l.length + 1) ≤ W) :
    rationalListSumBitCost model l ≤ (4 * l.length + 1) * model.rat W := by
  induction l with
  | nil =>
    have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hW
    simpa only [rationalListSumBitCost, hZero, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.one_mul]
      using (show 3 ≤ model.rat W from hW.trans (model.word_le W))
  | cons q rest ih =>
    have hq := hItems q (by simp)
    have hRest : ∀ r ∈ rest, RationalHeight r s := fun r hr => hItems r (by simp [hr])
    have hTail := RationalHeight.list_sum hRest
    have hFull := RationalHeight.list_sum hItems
    have hTailW : 1 + 2 * ((s + 1) * rest.length + 1) ≤ W := by
      simp only [List.length_cons, Nat.mul_succ] at hW
      omega
    have hHeadW : 1 + 2 * s ≤ W := by
      simp only [List.length_cons, Nat.mul_succ] at hW
      omega
    have hQ := (rationalWordWidth_of_height hq).trans hHeadW
    have hT := (rationalWordWidth_of_height hTail).trans hTailW
    have hF := (rationalWordWidth_of_height hFull).trans hW
    rw [List.sum_cons] at hF
    have hQPrice := hQ.trans (model.word_le W)
    have hTPrice := hT.trans (model.word_le W)
    have hFPrice := hF.trans (model.word_le W)
    have hCall := model.monotone (show RationalExpression.pairWidth q rest.sum ≤ W from max_le hQ hT)
    have hOld := ih hRest hTailW
    simp only [rationalListSumBitCost, List.length_cons]
    nlinarith

end Blotto
namespace Blotto.RationalWeightList

def massBitCost {α : Type*} (model : RationalCostModel) (l : RationalWeightList α) : ℕ :=
  rationalListSumBitCost model (l.items.map Prod.snd)

theorem massBitCost_bound {α : Type*} (model : RationalCostModel) (l : RationalWeightList α) (k s W : ℕ)
    (h : l.Bounded k s) (hW : 1 + 2 * ((s + 1) * k + 1) ≤ W) :
    l.massBitCost model ≤ (4 * k + 1) * model.rat W := by
  have hItems : ∀ q ∈ l.items.map Prod.snd, RationalHeight q s := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨item, hi, rfl⟩
    exact h.2 item hi
  have hLen : (l.items.map Prod.snd).length ≤ k := by simpa only [List.length_map] using h.1
  have hWidth : 1 + 2 * ((s + 1) * (l.items.map Prod.snd).length + 1) ≤ W := by
    have hm := Nat.mul_le_mul_left (s + 1) hLen
    omega
  exact (rationalListSumBitCost_bound model _ s W hItems hWidth).trans
    (Nat.mul_le_mul_right _ (by omega : 4 * (l.items.map Prod.snd).length + 1 ≤ 4 * k + 1))

end Blotto.RationalWeightList
