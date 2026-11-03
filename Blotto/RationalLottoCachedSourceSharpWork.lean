import Blotto.RationalLottoCachedSourceWork
import Blotto.WordMachineSerialSourceSharpWork

/-! The actual joined cached PRG controller retains the n−1 store bound.
The initial ready cursor performs no store, even before cap exhaustion. -/

namespace Blotto.RationalLottoResourceSystem

theorem cachedSourceStores_sharp_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceStores K R outerBits scalarBits choiceBits ≤ n - 1 := by
  have h := i.phase.runCachedSerialSourceWork_initial_bound
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.PhaseCursor => rationalResourceStoreCharge cursor.1) 1
    (fun cursor => rationalResourceStoreCharge_bound cursor.1) R i.start choiceBits
  change i.cachedSourceStores K R outerBits scalarBits choiceBits ≤ 1 * (i.phase.rank i.start) + 0 at h
  simpa only [Nat.one_mul, Nat.add_zero] using h.trans (by simpa using i.phase_rank)

theorem cachedSourceResourceWrites_sharp_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    2 * i.cachedSourceStores K R outerBits scalarBits choiceBits ≤ 2 * (n - 1) :=
  Nat.mul_le_mul_left 2 (i.cachedSourceStores_sharp_bound K R outerBits scalarBits choiceBits)

theorem cachedSourceStoreRamWork_sharp_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    20 * i.cachedSourceStores K R outerBits scalarBits choiceBits ≤ 20 * (n - 1) :=
  Nat.mul_le_mul_left 20 (i.cachedSourceStores_sharp_bound K R outerBits scalarBits choiceBits)

end Blotto.RationalLottoResourceSystem
