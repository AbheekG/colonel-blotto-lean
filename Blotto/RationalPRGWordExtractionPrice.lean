import Blotto.RationalLottoWordExtractionPrice
import Blotto.RationalPRGSourceBitPrice

/-! Both paper packets use the priced prepared source request, including
canonical integer-word extraction. The rich source is initially terminal. -/

namespace Blotto.RationalLottoResourceSystem

def paperSourceRequestBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.cachedSourceRequestBitCost model K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem paperSourceRequestBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    i.paperSourceRequestBitCost model K bits ≤ 98 * n * model.rat (3 + 2 * binaryWordWidth D) :=
  i.cachedSourceRequestBitCost_bound model D hD hB hL hR K _ _ _ _

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

theorem richCachedSourceRequestBitCost_eq_zero {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.richNativeSystem.cachedSourceRequestBitCost model K R outerBits scalarBits choiceBits = 0 := by
  have h := i.richNativeSystem.cachedSourceRequestBitCost_initial_bound model i.latticeDenominator
    i.latticeDenominator_pos (le_refl _) i.lengths_on_lattice i.richInitial_on_lattice K R outerBits scalarBits choiceBits
  have hRank : i.richNativeSystem.phase.rank i.richNativeSystem.start = 0 := i.richResource_rank_zero
  have hCharge : rationalResourcePairRequestCharge model i.richNativeSystem.start.1 = 0 := by
    apply RationalActiveResources.pairRequestBitCost_terminal
    change i.richState.active.length ≤ 1
    rw [i.richState_active_empty]
    simp
  rw [hRank, hCharge, Nat.mul_zero, Nat.add_zero] at h
  exact Nat.le_zero.mp h

def richPaperSourceRequestBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richNativeSystem.paperSourceRequestBitCost model K bits

def poorPaperSourceRequestBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorNativeSystem.paperSourceRequestBitCost model K bits

theorem richPaperSourceRequestBitCost_eq_zero {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richPaperSourceRequestBitCost model K bits = 0 := i.richCachedSourceRequestBitCost_eq_zero model K _ _ _ _

theorem poorPaperSourceRequestBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorPaperSourceRequestBitCost model K bits ≤ 98 * n * model.rat (5 + 2 * i.inputWordWidth) := by
  have h := i.poorNativeSystem.paperSourceRequestBitCost_bound model i.latticeDenominator
    i.latticeDenominator_pos i.b_le i.lengths_on_lattice i.poorInitial_on_lattice K bits
  have hWidth : 3 + 2 * binaryWordWidth i.latticeDenominator ≤ 5 + 2 * i.inputWordWidth := by
    have hw := i.latticeDenominator_wordWidth
    omega
  exact h.trans (Nat.mul_le_mul_left (98 * n) (model.monotone hWidth))

end Blotto.RationalPRGInput
