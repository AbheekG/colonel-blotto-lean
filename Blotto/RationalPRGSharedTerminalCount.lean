import Blotto.CachedSerialPreparationCount
import Blotto.RationalPRGSharedTerminalLedger

/-! Both primary paper packets prepare terminal data at most once. The rich
source is initially complete, so its count is exactly one at every bit cap. -/

namespace Blotto.RationalLottoResourceSystem

theorem sharedTerminalPreparationCount_zero_rank {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool)
    (hRank : i.phase.rank i.start = 0) : i.sharedTerminalPreparationCount K R outerBits scalarBits bits = 1 := by
  rw [i.sharedTerminalPreparationCount_refines]
  exact i.phase.cachedSerialPreparationCount_zero_rank
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    i.start hRank R bits 0 (Nat.zero_le R)

def sharedPaperTerminalPreparationCount {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedTerminalPreparationCount K (coinBitBudget n K)
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem sharedPaperTerminalPreparationCount_bound {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : i.sharedPaperTerminalPreparationCount K bits ≤ 1 :=
  i.sharedTerminalPreparationCount_bound K _ _ _ _

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

theorem richSharedPaperTerminalPreparationCount_eq_one {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richNativeSystem.sharedPaperTerminalPreparationCount K bits = 1 :=
  i.richNativeSystem.sharedTerminalPreparationCount_zero_rank K _ _ _ _ i.richResource_rank_zero

theorem poorSharedPaperTerminalPreparationCount_bound {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorNativeSystem.sharedPaperTerminalPreparationCount K bits ≤ 1 :=
  i.poorNativeSystem.sharedPaperTerminalPreparationCount_bound K bits

end Blotto.RationalPRGInput
