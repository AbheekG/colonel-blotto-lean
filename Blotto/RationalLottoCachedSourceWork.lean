import Blotto.RationalLottoProgram
import Blotto.RationalResourceStoreWork
import Blotto.WordMachineSerialSourceWork
import Blotto.RealPairProgram

/-! The production cached PRG controller has at most n source callbacks.
Its pair-preparation and selected pair-store components remain linear after
joining the terminal sampler. Prices below are rational/RAM operation labels;
integer/backend and physical ownership costs are separate. -/

namespace Blotto.RationalLottoResourceSystem

theorem fields_pos {n : ℕ} (i : RationalLottoResourceSystem n) : 0 < n := by
  cases n with
  | zero =>
    have h := i.initial_sum
    simp at h
    linarith [i.B_pos]
  | succ n => omega

def cachedSourceCallbacks {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun _ : i.PhaseCursor => 1))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem cachedSourceCallbacks_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceCallbacks K R outerBits scalarBits choiceBits ≤ n := by
  have h := i.phase.runCachedSerialSourceWork_bound
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun _ => 1) 1 (fun _ => le_rfl) R i.start choiceBits
  have hRank := i.phase_rank
  have hn := i.fields_pos
  change i.cachedSourceCallbacks K R outerBits scalarBits choiceBits ≤ 1 * (i.phase.rank i.start + 1) at h
  omega

def cachedSourcePairPreparationWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  RealPairProgram.preparationWork * i.cachedSourceCallbacks K R outerBits scalarBits choiceBits

theorem cachedSourcePairPreparationWork_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourcePairPreparationWork K R outerBits scalarBits choiceBits ≤ 96 * n := by
  unfold cachedSourcePairPreparationWork
  rw [RealPairProgram.preparationWork_eq]
  exact Nat.mul_le_mul_left 96 (i.cachedSourceCallbacks_bound K R outerBits scalarBits choiceBits)

def cachedSourceStores {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun cursor : i.PhaseCursor => rationalResourceStoreCharge cursor.1))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem cachedSourceStores_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceStores K R outerBits scalarBits choiceBits ≤ n := by
  have h := i.phase.runCachedSerialSourceWork_bound
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.PhaseCursor => rationalResourceStoreCharge cursor.1) 1
    (fun cursor => rationalResourceStoreCharge_bound cursor.1) R i.start choiceBits
  have hRank := i.phase_rank
  have hn := i.fields_pos
  change i.cachedSourceStores K R outerBits scalarBits choiceBits ≤ 1 * (i.phase.rank i.start + 1) at h
  omega

theorem cachedSourceResourceWrites_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    2 * i.cachedSourceStores K R outerBits scalarBits choiceBits ≤ 2 * n :=
  Nat.mul_le_mul_left 2 (i.cachedSourceStores_bound K R outerBits scalarBits choiceBits)

theorem cachedSourceStoreRamWork_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    20 * i.cachedSourceStores K R outerBits scalarBits choiceBits ≤ 20 * n :=
  Nat.mul_le_mul_left 20 (i.cachedSourceStores_bound K R outerBits scalarBits choiceBits)

end Blotto.RationalLottoResourceSystem
