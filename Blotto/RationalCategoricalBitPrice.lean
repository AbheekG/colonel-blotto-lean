import Blotto.RationalListSumBitCost
import Blotto.ProbabilityWordBitCost

/-! Actual categorical callbacks price the mass guard and, when positive, a
second mass evaluation, division and canonical coin-field extraction. No common
subexpression caching is assumed. Encoding, list/address and backend are separate. -/

namespace Blotto

def categoricalRequestWidth (k s : ℕ) : ℕ := 1 + 2 * ((s + 1) * (k + 1))

def categoricalMassGuardBitCost {α : Type*} (model : RationalCostModel) (l : RationalWeightList α) : ℕ :=
  l.massBitCost model + rationalWordWidth (0 : ℚ) + rationalWordWidth l.mass +
    model.rat (RationalExpression.pairWidth 0 l.mass)

def categoricalRatioBitCost (model : RationalCostModel) (head mass : ℚ) : ℕ :=
  rationalWordWidth head + rationalWordWidth mass + model.rat (RationalExpression.pairWidth head mass) +
    rationalWordWidth (head / mass) + (2 * rationalWordWidth (head / mass) - 1)

theorem categoricalRatioBitCost_fields (model : RationalCostModel) (head mass : ℚ)
    (hRatio : 0 ≤ head / mass ∧ head / mass ≤ 1) :
    categoricalRatioBitCost model head mass =
      rationalWordWidth head + rationalWordWidth mass + model.rat (RationalExpression.pairWidth head mass) +
        rationalWordWidth (head / mass) + ProbabilityWords.ofRatBitCost (head / mass) hRatio := by
  rw [ProbabilityWords.ofRatBitCost_eq]
  rfl

def categoricalCallbackBitCost {α : Type*} (model : RationalCostModel) : CategoricalState α → ℕ
  | .selected _ => 0
  | .remaining l => match l.items with
    | [] => 0
    | [_] => 0
    | head :: _next :: _tail => categoricalMassGuardBitCost model l +
        if 0 < l.mass then l.massBitCost model + categoricalRatioBitCost model head.2 l.mass else 0

theorem categoricalMassGuardBitCost_bound {α : Type*} (model : RationalCostModel)
    (l : RationalWeightList α) (k s : ℕ) (h : l.Bounded k s) :
    categoricalMassGuardBitCost model l ≤ (4 * k + 4) * model.rat (categoricalRequestWidth k s) := by
  let W := categoricalRequestWidth k s
  have hWidth : 1 + 2 * ((s + 1) * k + 1) ≤ W := by dsimp [W, categoricalRequestWidth]; nlinarith
  have hSum := l.massBitCost_bound model k s W h hWidth
  have hMass := (rationalWordWidth_of_height h.mass_height).trans hWidth
  have hZero : rationalWordWidth (0 : ℚ) ≤ W := by
    have hz : rationalWordWidth (0 : ℚ) = 3 := by decide
    rw [hz]
    dsimp [W, categoricalRequestWidth]
    nlinarith
  have hMassPrice := hMass.trans (model.word_le W)
  have hZeroPrice := hZero.trans (model.word_le W)
  have hCall := model.monotone (show RationalExpression.pairWidth 0 l.mass ≤ W from max_le hZero hMass)
  unfold categoricalMassGuardBitCost
  nlinarith

theorem categoricalRatioBitCost_bound {α : Type*} (model : RationalCostModel) (l : RationalWeightList α)
    (head : α × ℚ) (hHead : head ∈ l.items) (k s : ℕ) (h : l.Bounded k s) :
    categoricalRatioBitCost model head.2 l.mass ≤ 6 * model.rat (categoricalRequestWidth k s) := by
  let W := categoricalRequestWidth k s
  have hh := h.2 head hHead
  have hm := h.mass_height
  have hRatio : RationalHeight (head.2 / l.mass) ((s + 1) * (k + 1)) := by
    convert hh.div hm using 1; ring
  have hHeadW : rationalWordWidth head.2 ≤ W := by
    have hp := rationalWordWidth_of_height hh
    dsimp [W, categoricalRequestWidth]
    nlinarith
  have hMassW : rationalWordWidth l.mass ≤ W := by
    have hp := rationalWordWidth_of_height hm
    dsimp [W, categoricalRequestWidth]
    nlinarith
  have hRatioW := rationalWordWidth_of_height hRatio
  change rationalWordWidth (head.2 / l.mass) ≤ W at hRatioW
  have hHeadPrice := hHeadW.trans (model.word_le W)
  have hMassPrice := hMassW.trans (model.word_le W)
  have hRatioPrice := hRatioW.trans (model.word_le W)
  have hCall := model.monotone (show RationalExpression.pairWidth head.2 l.mass ≤ W from max_le hHeadW hMassW)
  change categoricalRatioBitCost model head.2 l.mass ≤ 6 * model.rat W
  unfold categoricalRatioBitCost
  omega

theorem categoricalCallbackBitCost_bound {α : Type*} (model : RationalCostModel) (cursor : CategoricalState α)
    (k s : ℕ) (h : cursor.Bounded k s) :
    categoricalCallbackBitCost model cursor ≤ (8 * k + 11) * model.rat (categoricalRequestWidth k s) := by
  cases cursor with
  | selected value => exact Nat.zero_le _
  | remaining l =>
    cases hi : l.items with
    | nil => simp only [categoricalCallbackBitCost, hi]; exact Nat.zero_le _
    | cons head rest =>
      cases hr : rest with
      | nil => simp only [categoricalCallbackBitCost, hi, hr]; exact Nat.zero_le _
      | cons next tail =>
        have hGuard := categoricalMassGuardBitCost_bound model l k s h
        have hWidth : 1 + 2 * ((s + 1) * k + 1) ≤ categoricalRequestWidth k s := by
          unfold categoricalRequestWidth; nlinarith
        have hSum := l.massBitCost_bound model k s _ h hWidth
        have hHead : head ∈ l.items := by rw [hi]; simp
        have hRatio := categoricalRatioBitCost_bound model l head hHead k s h
        simp only [categoricalCallbackBitCost, hi, hr]
        split_ifs <;> nlinarith

end Blotto
