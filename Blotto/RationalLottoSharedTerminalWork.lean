import Blotto.RationalLottoSharedHandoffRefinement
import Blotto.RationalLottoCachedTerminalWork

/-! Primary terminal packing/routing is charged at source completion at most
once. The charge survives later terminal exhaustion; source exhaustion pays zero.
Local-coupling preparation, output and physical/backend costs are separate. -/

namespace Blotto.RationalLottoResourceSystem

def sharedTerminalPreparationWork {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) : ℕ :=
  i.sharedHandoffWork K outerBits scalarBits
    (fun value => (i.terminalData value).packingAndRoutingBitCost model (binaryWordWidth (n + 4)))
    (fun _ _ => 0) R bits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem sharedTerminalPreparationWork_refines {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedTerminalPreparationWork model K R outerBits scalarBits bits =
      i.cachedTerminalPreparationWork model K R outerBits scalarBits bits := by
  refine (i.sharedHandoffWork_refines K outerBits scalarBits
    (fun value => (i.terminalData value).packingAndRoutingBitCost model (binaryWordWidth (n + 4)))
    (fun _ _ => 0) R bits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)).trans ?_
  simp only [handoffCharge, WordStateMachine.serialHandoffCharge_zeroTerminal]
  rfl

theorem sharedTerminalPreparationWork_bound {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedTerminalPreparationWork model K R outerBits scalarBits bits ≤
      (17 * n + 15) * model.rat (i.terminalCacheWidth D) := by
  rw [i.sharedTerminalPreparationWork_refines]
  exact i.cachedTerminalPreparationWork_bound model D hD hB hL K R outerBits scalarBits bits

def sharedTerminalPreparationCount {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) : ℕ :=
  i.sharedHandoffWork K outerBits scalarBits (fun _ => 1) (fun _ _ => 0)
    R bits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem sharedTerminalPreparationCount_refines {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedTerminalPreparationCount K R outerBits scalarBits bits =
      i.cachedTerminalPreparationCount K R outerBits scalarBits bits := by
  refine (i.sharedHandoffWork_refines K outerBits scalarBits (fun _ => 1) (fun _ _ => 0)
    R bits (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)).trans ?_
  simp only [handoffCharge, WordStateMachine.serialHandoffCharge_zeroTerminal]
  rfl

theorem sharedTerminalPreparationCount_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedTerminalPreparationCount K R outerBits scalarBits bits ≤ 1 := by
  rw [i.sharedTerminalPreparationCount_refines]
  exact i.cachedTerminalPreparationCount_bound K R outerBits scalarBits bits

theorem sharedHandoffWork_exhausted {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (cost : i.PhaseResult → ℕ)
    (terminalCharge : ∀ value : i.PhaseResult, ((i.terminalData value).program K outerBits scalarBits).State → ℕ)
    (N : ℕ) (bits : Fin N → Bool) {w : ℕ} (choice : ResourceChoice i.length) (a b : FixedBinaryWord w)
    (hb : 0 < b.value) (hab : a.value ≤ b.value)
    (hCursor : i.SharedInvariant (.coin choice a b hb hab)) (pos : ℕ) (hpos : pos ≤ N)
    (hz : a.isZero ≠ true) (he : a.same b ≠ true) (hEnd : ¬pos < N) :
    i.sharedHandoffWork K outerBits scalarBits cost terminalCharge N bits (.coin choice a b hb hab) hCursor pos hpos = 0 := by
  conv_lhs => unfold sharedHandoffWork
  simp only [dite_eq_right hz, dite_eq_right he, dite_eq_right hEnd]

end Blotto.RationalLottoResourceSystem
