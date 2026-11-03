import Blotto.RationalResourceWordExtractionPrice
import Blotto.RationalLottoSourceBitPrice

/-! Pair preparation plus canonical coin-word extraction follows the joined
production cached source path. The price excludes stores, classification,
control, Boolean encoding and physical backend/ownership work. -/

namespace Blotto.RationalLottoResourceSystem

def cachedSourceRequestBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun cursor : i.PhaseCursor => rationalResourcePairRequestCharge model cursor.1))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem cachedSourceRequestBitCost_initial_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceRequestBitCost model K R outerBits scalarBits choiceBits ≤
      (98 * model.rat (3 + 2 * binaryWordWidth D)) * i.phase.rank i.start +
        rationalResourcePairRequestCharge model i.start.1 := by
  apply i.phase.runCachedSerialSourceWork_initial_bound_under
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.PhaseCursor => rationalResourcePairInvariant i.length D cursor.1)
    (i.phase_pairLattice_closed D hL)
    (fun cursor : i.PhaseCursor => rationalResourcePairRequestCharge model cursor.1)
    (98 * model.rat (3 + 2 * binaryWordWidth D)) _ R i.start (i.phase_pairLattice_start D hR) choiceBits
  intro cursor hCursor
  exact cursor.1.materialize.pairRequestBitCost_bound model D hD hL (fun j => (i.length_le j).trans hB) hCursor

theorem cachedSourceRequestBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceRequestBitCost model K R outerBits scalarBits choiceBits ≤
      98 * n * model.rat (3 + 2 * binaryWordWidth D) := by
  let bound := 98 * model.rat (3 + 2 * binaryWordWidth D)
  have hWork := i.phase.runCachedSerialSourceWork_bound_under
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.PhaseCursor => rationalResourcePairInvariant i.length D cursor.1)
    (i.phase_pairLattice_closed D hL)
    (fun cursor : i.PhaseCursor => rationalResourcePairRequestCharge model cursor.1) bound
    (fun cursor hc => cursor.1.materialize.pairRequestBitCost_bound model D hD hL (fun j => (i.length_le j).trans hB) hc)
    R i.start (i.phase_pairLattice_start D hR) choiceBits
  change i.cachedSourceRequestBitCost model K R outerBits scalarBits choiceBits ≤ bound * (i.phase.rank i.start + 1) at hWork
  have hRank : i.phase.rank i.start + 1 ≤ n := by
    have hp := i.phase_rank
    have hn := i.fields_pos
    omega
  have hBudget := Nat.mul_le_mul_left bound hRank
  have hPrice : bound * n = 98 * n * model.rat (3 + 2 * binaryWordWidth D) := by dsimp [bound]; ring
  exact hWork.trans (hBudget.trans_eq hPrice)

end Blotto.RationalLottoResourceSystem
