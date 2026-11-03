import Blotto.RationalLottoStoreBitPrice
import Blotto.RationalPRGSourceBitPrice

/-! Deferred-store prices use the paper's exact bit blocks for both players.
The rich source performs no update. Logical writes have a linear allowance;
the separate full-copy allowance remains quadratic in the worst case. -/

namespace Blotto.RationalLottoResourceSystem

def paperSourceStoreBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.cachedSourceStoreBitCost model copyResources K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem paperSourceStoreBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (copyResources : Bool) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperSourceStoreBitCost model copyResources K bits ≤
      (if copyResources then 2 * n + 30 else 32) * (n - 1) * model.rat (8 * binaryWordWidth D + 23) :=
  i.cachedSourceStoreBitCost_bound model copyResources D hD hB hL hR K _ _ _ _

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

theorem richCachedSourceStoreBitCost_eq_zero {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.richNativeSystem.cachedSourceStoreBitCost model copyResources K R outerBits scalarBits choiceBits = 0 := by
  have h := i.richNativeSystem.cachedSourceStoreBitCost_initial_bound model copyResources i.latticeDenominator
    i.latticeDenominator_pos (le_refl _) i.lengths_on_lattice i.richInitial_on_lattice K R outerBits scalarBits choiceBits
  have hRank : i.richNativeSystem.phase.rank i.richNativeSystem.start = 0 := i.richResource_rank_zero
  rw [hRank, Nat.mul_zero] at h
  exact Nat.le_zero.mp h

def richPaperSourceStoreBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richNativeSystem.paperSourceStoreBitCost model copyResources K bits

def poorPaperSourceStoreBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorNativeSystem.paperSourceStoreBitCost model copyResources K bits

theorem richPaperSourceStoreBitCost_eq_zero {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richPaperSourceStoreBitCost model copyResources K bits = 0 :=
  i.richCachedSourceStoreBitCost_eq_zero model copyResources K _ _ _ _

theorem poorPaperSourceStoreBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorPaperSourceStoreBitCost model copyResources K bits ≤
      (if copyResources then 2 * n + 30 else 32) * (n - 1) * model.rat (8 * i.inputWordWidth + 31) := by
  have h := i.poorNativeSystem.paperSourceStoreBitCost_bound model copyResources i.latticeDenominator
    i.latticeDenominator_pos i.b_le i.lengths_on_lattice i.poorInitial_on_lattice K bits
  have hWidth : 8 * binaryWordWidth i.latticeDenominator + 23 ≤ 8 * i.inputWordWidth + 31 := by
    have hw := i.latticeDenominator_wordWidth
    omega
  exact h.trans (Nat.mul_le_mul_left ((if copyResources then 2 * n + 30 else 32) * (n - 1)) (model.monotone hWidth))

end Blotto.RationalPRGInput
