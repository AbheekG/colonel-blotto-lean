import Blotto.PreparedGroupHeight
import Blotto.RationalExpressionBitCost

/-! Cached routing emits one array row in a single coordinate pass. Prices
cover available group-value copies, coordinate rational primitives and writes.
Producing the small group vector, address/tag/list work, allocation and the
physical backend are separate; no array-reference uniqueness is assumed. -/

namespace Blotto.PreparedGroupOutput
open scoped BigOperators

def routedValue {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (y : Fin m → ℚ) (j : Fin n) : ℚ :=
  match (p.table.read j).1 with
  | none => 0
  | some g => (p.table.read j).2 * y g

theorem routedValue_eq {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (y : Fin m → ℚ) (j : Fin n) : p.routedValue y j = (p.emit y).allocation j := by
  simp only [routedValue, emit, RationalProportionalGroups.emit, RationalResourceArray.allocation_ofAllocation, FixedArrayTable.read_ofFn]
  rfl

def routedBitCost {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (y : Fin m → ℚ) (j : Fin n) : ℕ :=
  match (p.table.read j).1 with
  | none => rationalWordWidth (0 : ℚ)
  | some g => rationalWordWidth (p.table.read j).2 + rationalWordWidth (y g) +
      model.rat (RationalExpression.pairWidth (p.table.read j).2 (y g)) +
      rationalWordWidth ((p.table.read j).2 * y g)

theorem routedBitCost_bound {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (y : Fin m → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hCoefficients : ∀ j, RationalHeight (p.table.read j).2 s) (hY : ∀ g, RationalHeight (y g) s) (j : Fin n) :
    p.routedBitCost model y j ≤ 4 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  let W := 1 + 2 * expressionHeightBudget s 1
  have hm := expressionHeightBudget_ge_input s 1
  cases ht : (p.table.read j).1 with
  | none =>
    have hz : rationalWordWidth (0 : ℚ) = 3 := by decide
    have hZero : rationalWordWidth (0 : ℚ) ≤ W := by rw [hz]; dsimp [W]; omega
    have hp := hZero.trans (model.word_le W)
    change p.routedBitCost model y j ≤ 4 * model.rat W
    simp only [routedBitCost, ht]
    omega
  | some g =>
    have hc := (rationalWordWidth_of_height ((hCoefficients j).mono hm)).trans (model.word_le W)
    have hy := (rationalWordWidth_of_height ((hY g).mono hm)).trans (model.word_le W)
    have hProduct : RationalHeight ((p.table.read j).2 * y g) (expressionHeightBudget s 1) := by
      have hC : RationalHeight (p.table.read j).2 (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hCoefficients j
      have hV : RationalHeight (y g) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hY g
      exact hC.mul_level hV
    have ho := (rationalWordWidth_of_height hProduct).trans (model.word_le W)
    have hCall := model.monotone (show RationalExpression.pairWidth (p.table.read j).2 (y g) ≤ W from
      max_le (rationalWordWidth_of_height ((hCoefficients j).mono hm)) (rationalWordWidth_of_height ((hY g).mono hm)))
    change p.routedBitCost model y j ≤ 4 * model.rat W
    simp only [routedBitCost, ht]
    omega

def emitBitCost {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (y : Fin m → ℚ) : ℕ :=
  (∑ g, rationalWordWidth (y g)) + ∑ j, p.routedBitCost model y j

theorem emitBitCost_bound {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (y : Fin m → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hCoefficients : ∀ j, RationalHeight (p.table.read j).2 s) (hY : ∀ g, RationalHeight (y g) s) :
    p.emitBitCost model y ≤ (m + 4 * n) * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  have hSample : (∑ g, rationalWordWidth (y g)) ≤ m * model.rat (1 + 2 * expressionHeightBudget s 1) := by
    calc
      _ ≤ ∑ _g : Fin m, model.rat (1 + 2 * expressionHeightBudget s 1) := Finset.sum_le_sum (fun g _ =>
        (rationalWordWidth_of_height ((hY g).mono (expressionHeightBudget_ge_input s 1))).trans (model.word_le _))
      _ = _ := by simp
  have hPass : (∑ j, p.routedBitCost model y j) ≤ n * (4 * model.rat (1 + 2 * expressionHeightBudget s 1)) := by
    calc
      _ ≤ ∑ _j : Fin n, 4 * model.rat (1 + 2 * expressionHeightBudget s 1) := Finset.sum_le_sum (fun j _ =>
        p.routedBitCost_bound model y s hs hCoefficients hY j)
      _ = _ := by simp
  unfold emitBitCost
  nlinarith

def mixedCoordinateBitCost {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (pivot : Fin n) (y : Fin (m + 1) → ℚ) (j : Fin n) : ℕ :=
  let base := p.routedValue (fun g => y g.castSucc) j
  let extra := if j = pivot then y (Fin.last m) else 0
  p.routedBitCost model (fun g => y g.castSucc) j + rationalWordWidth base + rationalWordWidth extra +
    model.rat (RationalExpression.pairWidth base extra) + rationalWordWidth (base + extra)

theorem mixedCoordinateBitCost_bound {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (pivot : Fin n) (y : Fin (m + 1) → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hCoefficients : ∀ j, RationalHeight (p.table.read j).2 s) (hY : ∀ g, RationalHeight (y g) s) (j : Fin n) :
    p.mixedCoordinateBitCost model pivot y j ≤ 8 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  let base := p.routedValue (fun g => y g.castSucc) j
  let extra := if j = pivot then y (Fin.last m) else 0
  let W := 1 + 2 * expressionHeightBudget s 2
  have hBase : RationalHeight base (expressionHeightBudget s 1) := by
    dsimp only [base]
    rw [routedValue_eq]
    simpa only [max_self] using p.emit_of_coefficient_heights s s (by omega) hCoefficients _ (fun g => hY g.castSucc) j
  have hExtra : RationalHeight extra (expressionHeightBudget s 1) := by
    dsimp [extra]
    split_ifs
    · exact (hY _).mono (expressionHeightBudget_ge_input s 1)
    · exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 1))
  have hOut := hBase.add_level hExtra
  have hm := expressionHeightBudget_mono s (by decide : 1 ≤ 2)
  have hb := (rationalWordWidth_of_height (hBase.mono hm)).trans (model.word_le W)
  have he := (rationalWordWidth_of_height (hExtra.mono hm)).trans (model.word_le W)
  have ho := (rationalWordWidth_of_height hOut).trans (model.word_le W)
  have hCall := model.monotone (show RationalExpression.pairWidth base extra ≤ W from
    max_le (rationalWordWidth_of_height (hBase.mono hm)) (rationalWordWidth_of_height (hExtra.mono hm)))
  have hRoute := (p.routedBitCost_bound model (fun g => y g.castSucc) s hs hCoefficients (fun g => hY g.castSucc) j).trans
    (Nat.mul_le_mul_left 4 (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm) 1)))
  change p.routedBitCost model (fun g => y g.castSucc) j ≤ 4 * model.rat W at hRoute
  change p.mixedCoordinateBitCost model pivot y j ≤ 8 * model.rat W
  unfold mixedCoordinateBitCost
  change p.routedBitCost model (fun g => y g.castSucc) j + rationalWordWidth base + rationalWordWidth extra +
    model.rat (RationalExpression.pairWidth base extra) + rationalWordWidth (base + extra) ≤ 8 * model.rat W
  omega

def emitMixedBitCost {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (pivot : Fin n) (y : Fin (m + 1) → ℚ) : ℕ :=
  (∑ g, rationalWordWidth (y g)) + ∑ j, p.mixedCoordinateBitCost model pivot y j

theorem emitMixedBitCost_bound {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (model : RationalCostModel) (pivot : Fin n) (y : Fin (m + 1) → ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hCoefficients : ∀ j, RationalHeight (p.table.read j).2 s) (hY : ∀ g, RationalHeight (y g) s) :
    p.emitMixedBitCost model pivot y ≤ (m + 1 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hSample : (∑ g, rationalWordWidth (y g)) ≤ (m + 1) * model.rat (1 + 2 * expressionHeightBudget s 2) := by
    calc
      _ ≤ ∑ _g : Fin (m + 1), model.rat (1 + 2 * expressionHeightBudget s 2) := Finset.sum_le_sum (fun g _ =>
        (rationalWordWidth_of_height ((hY g).mono (expressionHeightBudget_ge_input s 2))).trans (model.word_le _))
      _ = _ := by simp
  have hPass : (∑ j, p.mixedCoordinateBitCost model pivot y j) ≤ n * (8 * model.rat (1 + 2 * expressionHeightBudget s 2)) := by
    calc
      _ ≤ ∑ _j : Fin n, 8 * model.rat (1 + 2 * expressionHeightBudget s 2) := Finset.sum_le_sum (fun j _ =>
        p.mixedCoordinateBitCost_bound model pivot y s hs hCoefficients hY j)
      _ = _ := by simp
  unfold emitMixedBitCost
  nlinarith

end Blotto.PreparedGroupOutput
