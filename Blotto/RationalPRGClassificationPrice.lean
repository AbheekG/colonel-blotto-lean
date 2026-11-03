import Blotto.RationalLottoClassificationPrice
import Blotto.RationalPRGStoreBitPrice

/-! Initial-data and selected retention-test prices specialize to both PRG
systems and the paper's exact bit blocks. These are operand/copy/comparison
components, with reader, address/list/control and physical costs separate. -/

namespace Blotto.RationalLottoResourceSystem

def paperSourceRetainedBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.cachedSourceRetainedBitCost model K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem paperSourceRetainedBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperSourceRetainedBitCost model K bits ≤ 10 * (n - 1) * model.rat (3 + 2 * binaryWordWidth D) :=
  i.cachedSourceRetainedBitCost_bound model D hD hB hL hR K _ _ _ _

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

def richInitialDataBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) : ℕ :=
  rationalInitialDataBitCost model i.richNativeSystem.length i.richNativeSystem.initial

def poorInitialDataBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) : ℕ :=
  rationalInitialDataBitCost model i.poorNativeSystem.length i.poorNativeSystem.initial

theorem richInitialDataBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) :
    i.richInitialDataBitCost model ≤ 7 * n * model.rat (5 + 2 * i.inputWordWidth) := by
  have h := i.richNativeSystem.initialDataBitCost_bound model i.latticeDenominator i.latticeDenominator_pos
    (le_refl _) i.lengths_on_lattice i.richInitial_on_lattice
  have hWidth : 3 + 2 * binaryWordWidth i.latticeDenominator ≤ 5 + 2 * i.inputWordWidth := by
    have hw := i.latticeDenominator_wordWidth
    omega
  exact h.trans (Nat.mul_le_mul_left (7 * n) (model.monotone hWidth))

theorem poorInitialDataBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) :
    i.poorInitialDataBitCost model ≤ 7 * n * model.rat (5 + 2 * i.inputWordWidth) := by
  have h := i.poorNativeSystem.initialDataBitCost_bound model i.latticeDenominator i.latticeDenominator_pos
    i.b_le i.lengths_on_lattice i.poorInitial_on_lattice
  have hWidth : 3 + 2 * binaryWordWidth i.latticeDenominator ≤ 5 + 2 * i.inputWordWidth := by
    have hw := i.latticeDenominator_wordWidth
    omega
  exact h.trans (Nat.mul_le_mul_left (7 * n) (model.monotone hWidth))

def richPaperSourceRetainedBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richNativeSystem.paperSourceRetainedBitCost model K bits

def poorPaperSourceRetainedBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorNativeSystem.paperSourceRetainedBitCost model K bits

theorem richCachedSourceRetainedBitCost_eq_zero {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.richNativeSystem.cachedSourceRetainedBitCost model K R outerBits scalarBits choiceBits = 0 := by
  have h := i.richNativeSystem.cachedSourceRetainedBitCost_initial_bound model i.latticeDenominator
    i.latticeDenominator_pos (le_refl _) i.lengths_on_lattice i.richInitial_on_lattice K R outerBits scalarBits choiceBits
  have hRank : i.richNativeSystem.phase.rank i.richNativeSystem.start = 0 := i.richResource_rank_zero
  rw [hRank, Nat.mul_zero] at h
  exact Nat.le_zero.mp h

theorem richPaperSourceRetainedBitCost_eq_zero {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richPaperSourceRetainedBitCost model K bits = 0 := i.richCachedSourceRetainedBitCost_eq_zero model K _ _ _ _

theorem poorPaperSourceRetainedBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorPaperSourceRetainedBitCost model K bits ≤ 10 * (n - 1) * model.rat (5 + 2 * i.inputWordWidth) := by
  have h := i.poorNativeSystem.paperSourceRetainedBitCost_bound model i.latticeDenominator
    i.latticeDenominator_pos i.b_le i.lengths_on_lattice i.poorInitial_on_lattice K bits
  have hWidth : 3 + 2 * binaryWordWidth i.latticeDenominator ≤ 5 + 2 * i.inputWordWidth := by
    have hw := i.latticeDenominator_wordWidth
    omega
  exact h.trans (Nat.mul_le_mul_left (10 * (n - 1)) (model.monotone hWidth))

end Blotto.RationalPRGInput
