import Blotto.SharedResourceWorkRefinement
import Blotto.CachedCallbackRestriction
import Blotto.CachedSerialSourceEquality
import Blotto.RationalLottoSharedRun

/-! The primary whole runner's source event observer follows its one-state
prefix and stops at terminal handoff. Arbitrary selected-update/preparation
prices equal the retained full serial observer; terminal work is separate. -/

namespace Blotto.RationalLottoResourceSystem

def sharedSourceCallbackWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (charge : RationalResourceCursor i.length → ℕ) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  SharedResourceCursor.runCallbackWork charge R i.initialState bits

theorem sharedSourceCallbackWork_refines {n : ℕ} (i : RationalLottoResourceSystem n)
    (charge : RationalResourceCursor i.length → ℕ) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedSourceCallbackWork charge R bits =
      (i.machine K outerBits scalarBits).runCachedCallbackWork
        (WordStateMachine.serialSourceCharge (fun q : i.PhaseCursor => charge q.1))
        R (i.samplingStart K outerBits scalarBits) bits := by
  rw [sharedSourceCallbackWork, SharedResourceCursor.runCallbackWork_refines]
  symm
  change (i.phase.serial _ _ 80 _).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun q : i.PhaseCursor => charge q.1)) R (.source i.start) bits = _
  rw [WordStateMachine.runCachedCallbackWork_serialSource]
  exact (rationalResourceMachine i.length).runCachedCallbackWork_restricted
    i.CursorInvariant i.TerminalState i.phaseProof charge R i.start bits

end Blotto.RationalLottoResourceSystem
