import Blotto.RationalRoutingBitCost
import Blotto.RationalLottoProgram
import Blotto.WordMachineSerialPreparationWork

/-! Terminal packing/routing prices specialize to the actual resource-phase
outputs. Serial callback work pays the selected preparation at most once;
source exhaustion does not trigger it. Other terminal/controller work is
outside this component ledger. -/

namespace Blotto.RationalLottoResourceSystem

def terminalCacheWidth {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ) : ℕ :=
  max (binaryWordWidth (n + 4)) (max (rationalWordWidth i.B) (3 + 2 * binaryWordWidth D))

theorem terminalPackingRouting_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (value : i.PhaseResult) :
    (i.terminalData value).packingAndRoutingBitCost model (binaryWordWidth (n + 4)) ≤
      (17 * n + 15) * model.rat (i.terminalCacheWidth D) :=
  (i.terminalData value).packingAndRoutingBitCost_input_width model D hD hB hL

def terminalPreparationWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCallbackWork
    (WordStateMachine.serialPreparationCharge i.phase
      (fun value => (i.terminalData value).packingAndRoutingBitCost model (binaryWordWidth (n + 4))))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem terminalPreparationWork_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.terminalPreparationWork model K R outerBits scalarBits choiceBits ≤
      (17 * n + 15) * model.rat (i.terminalCacheWidth D) :=
  i.phase.runSerialPreparationWork_bound
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun value => (i.terminalData value).packingAndRoutingBitCost model (binaryWordWidth (n + 4)))
    ((17 * n + 15) * model.rat (i.terminalCacheWidth D))
    (i.terminalPackingRouting_bound model D hD hB hL) R i.start choiceBits

def terminalPreparationCount {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCallbackWork
    (WordStateMachine.serialPreparationCharge i.phase (fun _ => 1))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem terminalPreparationCount_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.terminalPreparationCount K R outerBits scalarBits choiceBits ≤ 1 :=
  i.phase.runSerialPreparationWork_bound
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun _ => 1) 1 (fun _ => le_rfl) R i.start choiceBits

end Blotto.RationalLottoResourceSystem
