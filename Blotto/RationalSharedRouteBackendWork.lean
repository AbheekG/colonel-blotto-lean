import Blotto.RationalTerminalRouteBackendWork
import Blotto.RationalLottoOutputHeight
import Blotto.SharedTerminalWindowWork

/-! The terminal backend ledger is delegated at the actual primary source
handoff position. The source lattice validates only reached terminal values;
one build and selected emission reads retain the original cap and bit reader.
Full source/allocator/peak-space composition remains separate. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedRouteBackendWork {n : ℕ} {β : Type*} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (W : ℕ)
    (hFit : ∀ value : i.PhaseResult, ∀ e ∈ (RationalTerminalPacking.prepare (i.terminalData value)).routeStoreProgram,
      (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits
    (fun value pos hpos => (i.terminalData value).terminalRouteBackendWork model primitive W (hFit value) state
      K outerBits scalarBits R bits pos hpos)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedRouteBackendWork_bound {n : ℕ} {β : Type*} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hWidth : binaryWordWidth D ≤ s)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c W : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (hFit : ∀ value : i.PhaseResult, ∀ e ∈ (RationalTerminalPacking.prepare (i.terminalData value)).routeStoreProgram,
      (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedRouteBackendWork model primitive W hFit state K R outerBits scalarBits bits ≤
      RationalTerminalLotto.terminalRouteBackendBound model c n s W := by
  let A := RationalTerminalLotto.terminalRouteBackendBound model c n s W
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hp := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value pos hpos => (i.terminalData value).terminalRouteBackendWork model primitive W (hFit value) state
      K outerBits scalarBits R bits pos hpos) A 0
    (fun value hValue pos hpos => ((h.terminalData value hValue).terminalRouteBackendWork_bound hD hB s hs hWidth
      model primitive c W hPrimitive (hFit value) state K outerBits scalarBits R bits pos hpos).trans (Nat.le_add_right _ _))
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  have he : A + 0 * (R - 0) = A :=
    (congrArg (fun t : ℕ => A + t) (Nat.zero_mul (R - 0))).trans (Nat.add_zero A)
  exact hp.trans_eq he

end Blotto.RationalLottoResourceSystem
