import Blotto.RationalUniformGroupCompleteProcessing

/-! A nine-slot categorical/segment controller has the same indexed Boolean
allowance for any supplied bounded descriptor. This supports both uniform and
mixed two-group continuations, without an intermediate sampler or new cap. -/

namespace Blotto.RationalSegmentLottery

def nineControlWordHeight (s : ℕ) : ℕ := (s + 1) * 10

def nineBooleanControlWork {n : ℕ} (l : RationalSegmentLottery n 9) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (l.machine 0 K scalarBits).cachedControlWork (fun _ => true) (fun w => 4 * w) FixedWordCoin.bodyAllowance
    N bits (.state l.start) pos hpos

theorem HeightAt.nineBooleanControlWork_bound {n : ℕ} {l : RationalSegmentLottery n 9} {s : ℕ}
    (h : l.HeightAt s) (K : ℕ) (scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    l.nineBooleanControlWork K scalarBits N bits pos hpos ≤
      32 * nineControlWordHeight s + (24 * nineControlWordHeight s + 28) * (18 + 2 * (N - pos)) := by
  have hStart := rationalWeightList_bounded l.weight l.nonnegative s h.1
  have hClosed : ∀ state : CategoricalState (Fin 9), state.Bounded 9 s →
      ((l.machine 0 K scalarBits).step state).Postcondition (fun q => q.Bounded 9 s) (fun _ => True) := by
    intro state hState
    exact WordTransition.mapValue_statePostcondition (fun slot => l.point K slot scalarBits)
      (fun q => q.Bounded 9 s) ((categoricalMachine (0 : Fin 9)).step state)
      (categoricalTransition_bounded (0 : Fin 9) 9 s state hState)
  have hWords : ∀ state : CategoricalState (Fin 9), state.Bounded 9 s →
      ((l.machine 0 K scalarBits).step state).WordsHeight (nineControlWordHeight s) := by
    intro state hState
    exact WordTransition.mapValue_wordsHeight (fun slot => l.point K slot scalarBits)
      ((categoricalMachine (0 : Fin 9)).step state) _ (categoricalTransition_wordsHeight (0 : Fin 9) 9 s state hState)
  have hp := (l.machine 0 K scalarBits).cachedControlWork_state_bound_under _ _ hWords hClosed N bits l.start hStart
    8 (le_of_eq (l.machine_rank 0 K scalarBits)) pos hpos
  have he : 4 * nineControlWordHeight s * 8 + (24 * nineControlWordHeight s + 28) * (2 * 8 + 2 * (N - pos) + 2) =
    32 * nineControlWordHeight s + (24 * nineControlWordHeight s + 28) * (18 + 2 * (N - pos)) := by ring
  exact hp.trans_eq he

end Blotto.RationalSegmentLottery
