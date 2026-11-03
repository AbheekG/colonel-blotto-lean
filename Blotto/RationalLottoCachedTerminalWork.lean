import Blotto.CachedWordCallbackWork
import Blotto.RationalLottoTerminalWork

/-! The production cached-word path inherits the exact one-time terminal
packing/routing charge, with no numeric-controller-only cost assumption. -/

namespace Blotto.RationalLottoResourceSystem

def cachedTerminalPreparationWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialPreparationCharge i.phase
      (fun value => (i.terminalData value).packingAndRoutingBitCost model (binaryWordWidth (n + 4))))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem cachedTerminalPreparationWork_eq {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) :
    i.cachedTerminalPreparationWork model K R outerBits scalarBits choiceBits =
      i.terminalPreparationWork model K R outerBits scalarBits choiceBits :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork_eq _ R _ choiceBits

theorem cachedTerminalPreparationWork_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedTerminalPreparationWork model K R outerBits scalarBits choiceBits ≤
      (17 * n + 15) * model.rat (i.terminalCacheWidth D) := by
  rw [i.cachedTerminalPreparationWork_eq]
  exact i.terminalPreparationWork_bound model D hD hB hL K R outerBits scalarBits choiceBits

def cachedTerminalPreparationCount {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialPreparationCharge i.phase (fun _ => 1))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem cachedTerminalPreparationCount_eq {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedTerminalPreparationCount K R outerBits scalarBits choiceBits =
      i.terminalPreparationCount K R outerBits scalarBits choiceBits :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork_eq _ R _ choiceBits

theorem cachedTerminalPreparationCount_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedTerminalPreparationCount K R outerBits scalarBits choiceBits ≤ 1 := by
  rw [i.cachedTerminalPreparationCount_eq]
  exact i.terminalPreparationCount_bound K R outerBits scalarBits choiceBits

end Blotto.RationalLottoResourceSystem
