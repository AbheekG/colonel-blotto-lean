import Blotto.SharedResourceControlRefinement
import Blotto.CachedSerialSourceControl
import Blotto.CachedControlPrices
import Blotto.CachedControlZeroRank
import Blotto.RationalLottoSourceControllerWork
import Blotto.RationalLottoSharedRun

/-! Source encoding and Boolean coin work follow the primary one-state prefix.
Work refinement keeps the same full serial packet and charges no terminal coin.
The source rank supplies a sharper bound independent of terminal rank. -/

namespace Blotto.RationalLottoResourceSystem

def sharedSourceControlWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (encodingPrice coinPrice : ℕ → ℕ) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  SharedResourceCursor.controlWork encodingPrice coinPrice R bits (.ready i.initialState) 0 (Nat.zero_le R)

theorem sharedSourceControlWork_refines {n : ℕ} (i : RationalLottoResourceSystem n)
    (encodingPrice coinPrice : ℕ → ℕ) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedSourceControlWork encodingPrice coinPrice R bits =
      (i.machine K outerBits scalarBits).cachedControlWork WordStateMachine.serialSourceTag encodingPrice coinPrice
        R bits (.state (i.samplingStart K outerBits scalarBits)) 0 (Nat.zero_le R) := by
  rw [sharedSourceControlWork, SharedResourceCursor.controlWork_refines]
  symm
  change (i.phase.serial _ _ 80 _).cachedControlWork WordStateMachine.serialSourceTag encodingPrice coinPrice
    R bits ((CachedWordCursor.state i.start).mapState .source) 0 (Nat.zero_le R) = _
  rw [WordStateMachine.cachedControlWork_serialSource]
  exact (rationalResourceMachine i.length).cachedControlWork_restricted
    i.CursorInvariant i.TerminalState i.phaseProof (fun _ => true) encodingPrice coinPrice R bits
    (.state i.start) 0 (Nat.zero_le R)

def sharedSourceControllerWork {n : ℕ} (i : RationalLottoResourceSystem n) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  i.sharedSourceControlWork (fun w => 4 * w) FixedWordCoin.bodyAllowance R bits

theorem sharedSourceControllerWork_refines {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedSourceControllerWork R bits = i.sourceControllerEncodingAndWordWork K R outerBits scalarBits bits := by
  rw [sharedSourceControllerWork, i.sharedSourceControlWork_refines _ _ K R outerBits scalarBits bits,
    WordStateMachine.cachedControlWork_prices_refine]
  rfl

theorem raw_sourceTrackedWordsHeight {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ) (hD : 0 < D)
    (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j)) :
    ∀ cursor, rationalResourcePairInvariant i.length D cursor →
      ((rationalResourceMachine i.length).step cursor).TrackedWordsHeight (fun _ => true) (binaryWordWidth D) := by
  intro cursor hCursor
  have hp := rationalResourceMachine_wordsHeight i.length D hD hL (fun j => (i.length_le j).trans hB) cursor hCursor
  cases hs : (rationalResourceMachine i.length).step cursor with
  | done value => trivial
  | ask a b hb hab upper lower => rw [hs] at hp; exact fun _ => hp

theorem sharedSourceControllerWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ)
    (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) (R : ℕ) (bits : Fin R → Bool) :
    i.sharedSourceControllerWork R bits ≤ 4 * binaryWordWidth D * (n - 1) +
      (24 * binaryWordWidth D + 28) * (2 * (n - 1) + 2 * R + 2) := by
  rw [sharedSourceControllerWork, sharedSourceControlWork, SharedResourceCursor.controlWork_refines,
    WordStateMachine.cachedControlWork_prices_refine]
  exact (rationalResourceMachine i.length).runCachedTrackedPreparationAndWordWork_rank_bound
    (rationalResourcePairInvariant i.length D) (fun _ => true) (binaryWordWidth D)
    (i.raw_sourceTrackedWordsHeight D hD hB hL)
    (rationalResourcePairInvariant_closed i.length D hL) R (n - 1) (.ready i.initialState)
    (rationalResourcePairInvariant_initial i.length i.initial D hR)
    (rationalResourceMachine_initial_rank i.length i.initial) bits

theorem sharedSourceControllerWork_zero_rank {n : ℕ} (i : RationalLottoResourceSystem n)
    (R : ℕ) (bits : Fin R → Bool) (hRank : i.phase.rank i.start = 0) :
    i.sharedSourceControllerWork R bits = 0 := by
  rw [sharedSourceControllerWork, sharedSourceControlWork, SharedResourceCursor.controlWork_refines]
  exact (rationalResourceMachine i.length).cachedControlWork_state_zero_rank (fun _ => true)
    (fun w => 4 * w) FixedWordCoin.bodyAllowance R bits (.ready i.initialState) hRank 0 (Nat.zero_le R)

end Blotto.RationalLottoResourceSystem
