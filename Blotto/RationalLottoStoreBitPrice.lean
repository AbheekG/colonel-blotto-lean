import Blotto.RationalResourceStoreBitPrice
import Blotto.RationalLottoSourceBitPrice

/-! Reached deferred-store prices on the joined cached PRG controller.
The initial ready state pays no store, yielding the n−1 update allowance.
The resource-copy flag keeps the native-copy obligation explicit. -/

namespace Blotto.RationalLottoResourceSystem

theorem phase_storeInvariant_closed {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j)) :
    ∀ cursor : i.PhaseCursor, rationalResourceStoreInvariant i.length D cursor.1 →
      (i.phase.step cursor).Postcondition
        (fun q => rationalResourceStoreInvariant i.length D q.1) (fun _ => True) :=
  (rationalResourceMachine i.length).restricted_additionalClosed i.CursorInvariant i.TerminalState i.phaseProof
    (rationalResourceStoreInvariant i.length D)
    (rationalResourceStoreInvariant_closed i.length D hL (fun j => (i.length_le j).trans hB))

theorem phase_storeInvariant_start {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ) (hB : i.B ≤ 1)
    (hR : ∀ j, OnRationalLattice D (i.initial j)) : rationalResourceStoreInvariant i.length D i.start.1 :=
  rationalResourceStoreInvariant_initial i.length i.initial D hR
    (fun j => ⟨(i.initial_box j).1, ((i.initial_box j).2.trans (i.length_le j)).trans hB⟩)

def cachedSourceStoreBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (copyResources : Bool) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge
      (fun cursor : i.PhaseCursor => rationalResourceStoreBitCharge model copyResources cursor.1))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem cachedSourceStoreBitCost_initial_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (copyResources : Bool) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceStoreBitCost model copyResources K R outerBits scalarBits choiceBits ≤
      ((if copyResources then 2 * n + 30 else 32) * model.rat (8 * binaryWordWidth D + 23)) * i.phase.rank i.start := by
  have h := i.phase.runCachedSerialSourceWork_initial_bound_under
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.PhaseCursor => rationalResourceStoreInvariant i.length D cursor.1)
    (i.phase_storeInvariant_closed D hB hL)
    (fun cursor : i.PhaseCursor => rationalResourceStoreBitCharge model copyResources cursor.1)
    ((if copyResources then 2 * n + 30 else 32) * model.rat (8 * binaryWordWidth D + 23))
    (fun cursor hc => rationalResourceStoreBitCharge_bound i.length model copyResources D hD hL
      (fun j => (i.length_le j).trans hB) cursor.1 hc)
    R i.start (i.phase_storeInvariant_start D hB hR) choiceBits
  change i.cachedSourceStoreBitCost model copyResources K R outerBits scalarBits choiceBits ≤
    ((if copyResources then 2 * n + 30 else 32) * model.rat (8 * binaryWordWidth D + 23)) * i.phase.rank i.start + 0 at h
  simpa only [Nat.add_zero] using h

theorem cachedSourceStoreBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (copyResources : Bool) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceStoreBitCost model copyResources K R outerBits scalarBits choiceBits ≤
      (if copyResources then 2 * n + 30 else 32) * (n - 1) * model.rat (8 * binaryWordWidth D + 23) := by
  have h := i.cachedSourceStoreBitCost_initial_bound model copyResources D hD hB hL hR K R outerBits scalarBits choiceBits
  have hRank := Nat.mul_le_mul_left
    ((if copyResources then 2 * n + 30 else 32) * model.rat (8 * binaryWordWidth D + 23)) i.phase_rank
  have hPrice : ((if copyResources then 2 * n + 30 else 32) * model.rat (8 * binaryWordWidth D + 23)) * (n - 1) =
      (if copyResources then 2 * n + 30 else 32) * (n - 1) * model.rat (8 * binaryWordWidth D + 23) := by ring
  exact h.trans (hRank.trans_eq hPrice)

end Blotto.RationalLottoResourceSystem
