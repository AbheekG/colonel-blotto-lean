import Blotto.RationalFractionalTestCost
import Blotto.RationalActiveResources
import Blotto.RationalUnitLatticeHeight

/-! Exact strict-test refinements and data-word prices for initialization and
the two-entry retained scan. List/address/control and reader execution costs
are separate from these copied-word and rational-comparison prices. -/

namespace Blotto
open scoped BigOperators

theorem rationalRetainedPair_reference {n : ℕ} (L : Fin n → ℚ) (resource : RationalResourceArray n) (a b : Fin n) :
    rationalRetainedPair L resource a b =
      [a, b].filter (fun j => decide (0 < resource.allocation j ∧ resource.allocation j < L j)) := by
  simp only [rationalRetainedPair, rationalFractionalAt_function]

theorem rationalInitialActive_reference {n : ℕ} (L r : Fin n → ℚ) :
    (RationalActiveResources.initial L r).active =
      (List.finRange n).filter (fun j => decide (0 < r j ∧ r j < L j)) := by
  simp only [RationalActiveResources.initial, RationalResourceArray.allocation_ofAllocation, rationalFractionalAt_function]

def rationalInitialFractionalBitCost {n : ℕ} (model : RationalCostModel) (L r : Fin n → ℚ) : ℕ :=
  ((List.finRange n).map (rationalFractionalBitCost model L r)).sum

def rationalInitialResourceCopyBitCost {n : ℕ} (r : Fin n → ℚ) : ℕ :=
  2 * ∑ j, rationalWordWidth (r j)

def rationalInitialDataBitCost {n : ℕ} (model : RationalCostModel) (L r : Fin n → ℚ) : ℕ :=
  rationalInitialResourceCopyBitCost r + rationalInitialFractionalBitCost model L r

theorem rationalInitialFractionalBitCost_bound {n : ℕ} (model : RationalCostModel) (L r : Fin n → ℚ) (W : ℕ)
    (hZero : rationalWordWidth (0 : ℚ) ≤ W) (hL : ∀ j, rationalWordWidth (L j) ≤ W)
    (hR : ∀ j, rationalWordWidth (r j) ≤ W) :
    rationalInitialFractionalBitCost model L r ≤ 5 * n * model.rat W := by
  have hSum : ((List.finRange n).map (rationalFractionalBitCost model L r)).sum ≤
      ((List.finRange n).map (fun _ => 5 * model.rat W)).sum :=
    List.sum_le_sum (fun j _ => rationalFractionalBitCost_bound model L r j W hZero (hL j) (hR j))
  have hConst : ((List.finRange n).map (fun _ => 5 * model.rat W)).sum = 5 * n * model.rat W := by simp; ring
  exact hSum.trans_eq hConst

theorem rationalInitialDataBitCost_bound {n : ℕ} (model : RationalCostModel) (L r : Fin n → ℚ) (W : ℕ)
    (hZero : rationalWordWidth (0 : ℚ) ≤ W) (hL : ∀ j, rationalWordWidth (L j) ≤ W)
    (hR : ∀ j, rationalWordWidth (r j) ≤ W) : rationalInitialDataBitCost model L r ≤ 7 * n * model.rat W := by
  have hScan := rationalInitialFractionalBitCost_bound model L r W hZero hL hR
  have hSum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => rationalWordWidth (r j)) (g := fun _ => model.rat W)
    (fun j _ => (hR j).trans (model.word_le W))
  have hConst : (∑ _j : Fin n, model.rat W) = n * model.rat W := by simp
  have hCopies := hSum.trans_eq hConst
  unfold rationalInitialDataBitCost rationalInitialResourceCopyBitCost
  nlinarith

def rationalRetainedFractionalBitCost {n : ℕ} (model : RationalCostModel) (L : Fin n → ℚ)
    (resource : RationalResourceArray n) (a b : Fin n) : ℕ :=
  rationalFractionalBitCost model L resource.allocation a + rationalFractionalBitCost model L resource.allocation b

theorem rationalRetainedFractionalBitCost_bound {n : ℕ} (model : RationalCostModel) (L : Fin n → ℚ)
    (resource : RationalResourceArray n) (a b : Fin n) (W : ℕ)
    (hZero : rationalWordWidth (0 : ℚ) ≤ W) (hL : ∀ j, rationalWordWidth (L j) ≤ W)
    (hR : ∀ j, rationalWordWidth (resource.allocation j) ≤ W) :
    rationalRetainedFractionalBitCost model L resource a b ≤ 10 * model.rat W := by
  have ha := rationalFractionalBitCost_bound model L resource.allocation a W hZero (hL a) (hR a)
  have hb := rationalFractionalBitCost_bound model L resource.allocation b W hZero (hL b) (hR b)
  unfold rationalRetainedFractionalBitCost
  omega

theorem rationalFractionalWordBound_lattice {D : ℕ} (hD : 0 < D) {q : ℚ}
    (hQ : OnRationalLattice D q) (hUnit : 0 ≤ q ∧ q ≤ 1) :
    rationalWordWidth q ≤ 3 + 2 * binaryWordWidth D := by
  have h := rationalWordWidth_of_height (rationalHeight_unit_lattice hD hQ hUnit)
  omega

end Blotto
