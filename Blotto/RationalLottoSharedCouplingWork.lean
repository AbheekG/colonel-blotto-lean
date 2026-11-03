import Blotto.SharedTerminalWindowWork
import Blotto.RationalTerminalGroupInputCost
import Blotto.RationalLottoOutputHeight

/-! The primary shared runner delegates coupling/input/emission work exactly
at source completion, using the same reader and advanced position. The source
lattice supplies terminal input heights. Prefix/packing/fallback and physical
metadata/backend/ownership remain separate. -/

namespace Blotto.RationalLottoResourceSystem

noncomputable def sharedCouplingAndEmissionWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) : ℕ :=
  i.sharedTerminalWindowWork R bits
    (fun value pos hpos => (i.terminalData value).inputCouplingAndEmissionAllowance model primitive copyResources K
      outerBits scalarBits R bits pos hpos)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le R)

theorem OnLattice.sharedCouplingAndEmissionWork_bound {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (bits : Fin R → Bool) :
    i.sharedCouplingAndEmissionWork model primitive copyResources K R outerBits scalarBits bits ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        (70000020 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 75) +
          320 * RationalTerminalLotto.terminalCouplingWordHeight (max s (K + 2)) +
            (24 * RationalTerminalLotto.terminalCouplingWordHeight (max s (K + 2)) + 28) * (162 + 2 * R) := by
  let H := RationalTerminalLotto.terminalCouplingWordHeight (max s (K + 2))
  let A := 9072 * RationalNestedInput.preparationNumericBitWork c K +
    (70000020 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 75) + 320 * H + 162 * (24 * H + 28)
  let B := 2 * (24 * H + 28)
  have hInitial : (SharedResourceCursor.ready i.initialState).OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hp := i.sharedTerminalWindowWork_bound D h.1 R bits
    (fun value pos hpos => (i.terminalData value).inputCouplingAndEmissionAllowance model primitive copyResources K
      outerBits scalarBits R bits pos hpos) A B
    (fun value hValue pos hpos => by
      have ht := (h.terminalData value hValue).inputCouplingAndEmissionAllowance_bound hD hB s hs hBudget hWidth
        model primitive c hPrimitive copyResources K outerBits scalarBits R bits pos hpos
      have he : 9072 * RationalNestedInput.preparationNumericBitWork c K +
          (70000020 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 75) +
            320 * H + (24 * H + 28) * (162 + 2 * (R - pos)) = A + B * (R - pos) := by dsimp [A, B]; ring
      exact ht.trans_eq he)
    (.ready i.initialState) i.initial_invariant hInitial 0 (Nat.zero_le R)
  have he : A + B * (R - 0) = 9072 * RationalNestedInput.preparationNumericBitWork c K +
      (70000020 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 75) +
        320 * H + (24 * H + 28) * (162 + 2 * R) := by dsimp [A, B]; ring
  exact hp.trans_eq he

end Blotto.RationalLottoResourceSystem
