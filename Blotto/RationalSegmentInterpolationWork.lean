import Blotto.RationalInterpolationBitCost
import Blotto.RationalLotteryHeight
import Blotto.RationalSegmentMachine
import Blotto.CachedEmissionBounds

/-! Native segment output is the priced interpolation expression in every
coordinate. Prices cover available endpoint/scalar copies and output words;
dyadic decoding, categorical preparation, descriptor reads and backend remain
separate. The emission charge is paid on a chosen slot only, including padding. -/

namespace Blotto.RationalSegmentLottery
open scoped BigOperators

def interpolationBitCost {n k : ℕ} (l : RationalSegmentLottery n k) (model : RationalCostModel)
    (K : ℕ) (scalarBits : Fin K → Bool) (slot : Fin k) : ℕ :=
  ∑ j, RationalInterpolationCode.materializedBitCost model (l.P slot j) (l.Q slot j)
    (dyadicMidpointSample K scalarBits)

theorem interpolation_value_eq {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ)
    (scalarBits : Fin K → Bool) (slot : Fin k) (j : Fin n) :
    RationalInterpolationCode.program.value (RationalInterpolationCode.environment
      (l.P slot j) (l.Q slot j) (dyadicMidpointSample K scalarBits)) = l.point K slot scalarBits j := by
  rw [RationalInterpolationCode.value_eq]
  rfl

theorem HeightAt.interpolationBitCost_bound {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (hs : 2 ≤ s) (model : RationalCostModel) (K : ℕ)
    (scalarBits : Fin K → Bool) (slot : Fin k) :
    l.interpolationBitCost model K scalarBits slot ≤
      13 * n * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 3) := by
  let w := max s (K + 2)
  have hw : 2 ≤ w := hs.trans (le_max_left _ _)
  have ht := (dyadicMidpointSample_height K scalarBits).mono (le_max_right s (K + 2))
  calc
    _ ≤ ∑ _j : Fin n, 13 * model.rat (1 + 2 * expressionHeightBudget w 3) :=
      Finset.sum_le_sum (fun j _ => RationalInterpolationCode.materializedBitCost_bound model _ _ _ w hw
        ((h.2 slot j).1.mono (le_max_left s (K + 2)))
        ((h.2 slot j).2.mono (le_max_left s (K + 2))) ht)
    _ = _ := by simp; ring

theorem HeightAt.interpolationEmissionWork_bound {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (hs : 2 ≤ s) (model : RationalCostModel) (fallback : Fin k)
    (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (categoricalMachine fallback).cachedEmissionWork (l.interpolationBitCost model K scalarBits)
      N bits (.state l.start) pos hpos ≤
        13 * n * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 3) := by
  apply (categoricalMachine fallback).cachedEmissionWork_bound_under (fun _ => True) _ _ _ N bits l.start trivial pos hpos
  intro state _
  cases ht : (categoricalMachine fallback).step state with
  | done slot => exact h.interpolationBitCost_bound hs model K scalarBits slot
  | ask a b hb hab upper lower => exact ⟨trivial, trivial⟩

def interpolationArithmeticWork (n : ℕ) : ℕ := 9 * n

theorem interpolationArithmeticWork_bound {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ)
    (scalarBits : Fin K → Bool) (slot : Fin k) :
    (∑ j : Fin n, (RationalInterpolationCode.program.run (RationalInterpolationCode.environment
      (l.P slot j) (l.Q slot j) (dyadicMidpointSample K scalarBits))).2) ≤ interpolationArithmeticWork n := by
  calc
    _ ≤ ∑ _j : Fin n, 9 := Finset.sum_le_sum (fun j _ => RationalInterpolationCode.arithmetic_primitives _ _ _)
    _ = _ := by simp [interpolationArithmeticWork, Nat.mul_comm]

end Blotto.RationalSegmentLottery
