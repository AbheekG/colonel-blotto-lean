import Blotto.RationalResourceWordHeight
import Blotto.WordMachineSerialTrackedWords
import Blotto.RationalLottoSourceBitPrice

/-! Source-only Boolean word work and encoding follow the full joined cached
controller. Source words retain the input lattice bound; continuation words
are left intact and uncharged by this component. -/

namespace Blotto.RationalLottoResourceSystem

theorem phase_wordsHeight {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ) (hD : 0 < D)
    (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j)) :
    ∀ cursor : i.PhaseCursor, rationalResourcePairInvariant i.length D cursor.1 →
      (i.phase.step cursor).WordsHeight (binaryWordWidth D) := by
  intro cursor hCursor
  exact WordTransition.restrict_wordsHeight i.CursorInvariant i.TerminalState
    ((rationalResourceMachine i.length).step cursor.1) (i.phaseProof cursor.1 cursor.2) _
    (rationalResourceMachine_wordsHeight i.length D hD hL (fun j => (i.length_le j).trans hB) cursor.1 hCursor)

def SourceControllerInvariant {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (D : ℕ) : i.SamplingState K outerBits scalarBits → Prop :=
  WordStateMachine.serialInvariant (fun cursor : i.PhaseCursor => rationalResourcePairInvariant i.length D cursor.1)

theorem sourceController_trackedWordsBounded {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    (i.machine K outerBits scalarBits).CachedTrackedWordsBounded
      (i.SourceControllerInvariant K outerBits scalarBits D) WordStateMachine.serialSourceTag
      (binaryWordWidth D) R choiceBits (.state (i.samplingStart K outerBits scalarBits)) 0 (Nat.zero_le R) := by
  apply (i.machine K outerBits scalarBits).runCached_trackedWordsBounded
    (i.SourceControllerInvariant K outerBits scalarBits D) WordStateMachine.serialSourceTag (binaryWordWidth D)
  · exact i.phase.serial_sourceTrackedWordsHeight
      (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
      (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
      (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
      (fun cursor : i.PhaseCursor => rationalResourcePairInvariant i.length D cursor.1) (binaryWordWidth D)
      (i.phase_wordsHeight D hD hB hL)
  · exact i.phase.serialInvariant_closed
      (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
      (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
      (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
      (fun cursor : i.PhaseCursor => rationalResourcePairInvariant i.length D cursor.1) (i.phase_pairLattice_closed D hL)
  · exact i.phase_pairLattice_start D hR

def sourceControllerWordWork {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).cachedTrackedWordWork WordStateMachine.serialSourceTag
    R choiceBits (.state (i.samplingStart K outerBits scalarBits)) 0 (Nat.zero_le R)

def sourceControllerEncodingCells {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).cachedTrackedEncodingCells WordStateMachine.serialSourceTag
    R choiceBits (.state (i.samplingStart K outerBits scalarBits)) 0 (Nat.zero_le R)

def sourceControllerEncodingAndWordWork {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).cachedTrackedPreparationAndWordWork WordStateMachine.serialSourceTag
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem sourceControllerWordWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.sourceControllerWordWork K R outerBits scalarBits choiceBits ≤
      (24 * binaryWordWidth D + 28) * (2 * (n - 1 + 80) + 2 * R + 2) := by
  have hp := i.sourceController_trackedWordsBounded D hD hB hL hR K R outerBits scalarBits choiceBits
  have hw := (i.machine K outerBits scalarBits).cachedTrackedWordWork_visits
    (i.SourceControllerInvariant K outerBits scalarBits D) WordStateMachine.serialSourceTag
    (binaryWordWidth D) R choiceBits (.state (i.samplingStart K outerBits scalarBits)) 0 (Nat.zero_le R) hp
  have hc := ((i.machine K outerBits scalarBits).runCachedCounts_bounds R (n - 1 + 80)
    (i.samplingStart K outerBits scalarBits) (i.program K outerBits scalarBits).rank_le choiceBits).2
  rw [FixedWordCoin.bodyAllowance_eq] at hw
  exact hw.trans (Nat.mul_le_mul_left _ hc)

theorem sourceControllerEncodingCells_bound {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.sourceControllerEncodingCells K R outerBits scalarBits choiceBits ≤ 2 * binaryWordWidth D * (n - 1 + 80) := by
  have hp := i.sourceController_trackedWordsBounded D hD hB hL hR K R outerBits scalarBits choiceBits
  have he := (i.machine K outerBits scalarBits).cachedTrackedEncodingCells_requests
    (i.SourceControllerInvariant K outerBits scalarBits D) WordStateMachine.serialSourceTag
    (binaryWordWidth D) R choiceBits (.state (i.samplingStart K outerBits scalarBits)) 0 (Nat.zero_le R) hp
  have hc := (i.machine K outerBits scalarBits).runCachedRequests_bound R (n - 1 + 80)
    (i.samplingStart K outerBits scalarBits) (i.program K outerBits scalarBits).rank_le choiceBits
  exact he.trans (Nat.mul_le_mul_left _ hc)

theorem sourceControllerEncodingAndWordWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.sourceControllerEncodingAndWordWork K R outerBits scalarBits choiceBits ≤
      4 * binaryWordWidth D * (n - 1 + 80) +
        (24 * binaryWordWidth D + 28) * (2 * (n - 1 + 80) + 2 * R + 2) := by
  have he := i.sourceControllerEncodingCells_bound D hD hB hL hR K R outerBits scalarBits choiceBits
  have hw := i.sourceControllerWordWork_bound D hD hB hL hR K R outerBits scalarBits choiceBits
  change 2 * i.sourceControllerEncodingCells K R outerBits scalarBits choiceBits +
    i.sourceControllerWordWork K R outerBits scalarBits choiceBits ≤ _
  nlinarith

end Blotto.RationalLottoResourceSystem
