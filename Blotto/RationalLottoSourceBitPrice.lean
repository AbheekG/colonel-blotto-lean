import Blotto.RationalResourcePairBitPrice
import Blotto.WordMachineSerialClosedWork
import Blotto.WordMachineAdditionalInvariant
import Blotto.RationalLottoCachedSourceWork

/-! Actual source-pair primitive prices accumulate linearly on the joined
production cached PRG path. Only the reached resource lattice is required;
continuation callbacks add no source-pair charge. Stores/control, probability
word extraction and the physical backend remain separate components. -/

namespace Blotto.RationalLottoResourceSystem

theorem phase_pairLattice_closed {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (i.length j)) :
    ∀ cursor : i.PhaseCursor, rationalResourcePairInvariant i.length D cursor.1 →
      (i.phase.step cursor).Postcondition
        (fun q => rationalResourcePairInvariant i.length D q.1) (fun _ => True) :=
  (rationalResourceMachine i.length).restricted_additionalClosed i.CursorInvariant i.TerminalState i.phaseProof
    (rationalResourcePairInvariant i.length D) (rationalResourcePairInvariant_closed i.length D hL)

theorem phase_pairLattice_start {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hR : ∀ j, OnRationalLattice D (i.initial j)) :
    rationalResourcePairInvariant i.length D i.start.1 :=
  rationalResourcePairInvariant_initial i.length i.initial D hR

def cachedSourcePairBitCost {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun cursor : i.PhaseCursor => rationalResourcePairCharge model cursor.1))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem cachedSourcePairBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourcePairBitCost model K R outerBits scalarBits choiceBits ≤
      96 * n * model.rat (3 + 2 * binaryWordWidth D) := by
  let bound := 96 * model.rat (3 + 2 * binaryWordWidth D)
  have hCharge : ∀ cursor : i.PhaseCursor, rationalResourcePairInvariant i.length D cursor.1 →
      rationalResourcePairCharge model cursor.1 ≤ bound := by
    intro cursor hCursor
    exact cursor.1.materialize.pairBitCost_bound model D hD hL (fun j => (i.length_le j).trans hB) hCursor
  have hWork := i.phase.runCachedSerialSourceWork_bound_under
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.PhaseCursor => rationalResourcePairInvariant i.length D cursor.1)
    (i.phase_pairLattice_closed D hL)
    (fun cursor : i.PhaseCursor => rationalResourcePairCharge model cursor.1) bound hCharge
    R i.start (i.phase_pairLattice_start D hR) choiceBits
  change i.cachedSourcePairBitCost model K R outerBits scalarBits choiceBits ≤ bound * (i.phase.rank i.start + 1) at hWork
  have hRank : i.phase.rank i.start + 1 ≤ n := by
    have hp := i.phase_rank
    have hn := i.fields_pos
    omega
  have hBudget := Nat.mul_le_mul_left bound hRank
  have hPrice : bound * n = 96 * n * model.rat (3 + 2 * binaryWordWidth D) := by dsimp [bound]; ring
  exact hWork.trans (hBudget.trans_eq hPrice)

theorem cachedSourcePairBitCost_initial_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourcePairBitCost model K R outerBits scalarBits choiceBits ≤
      (96 * model.rat (3 + 2 * binaryWordWidth D)) * i.phase.rank i.start +
        rationalResourcePairCharge model i.start.1 := by
  apply i.phase.runCachedSerialSourceWork_initial_bound_under
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.PhaseCursor => rationalResourcePairInvariant i.length D cursor.1)
    (i.phase_pairLattice_closed D hL)
    (fun cursor : i.PhaseCursor => rationalResourcePairCharge model cursor.1)
    (96 * model.rat (3 + 2 * binaryWordWidth D))
    _ R i.start (i.phase_pairLattice_start D hR) choiceBits
  intro cursor hCursor
  exact cursor.1.materialize.pairBitCost_bound model D hD hL (fun j => (i.length_le j).trans hB) hCursor

end Blotto.RationalLottoResourceSystem
