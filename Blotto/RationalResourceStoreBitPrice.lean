import Blotto.PairStoreBitCost
import Blotto.RationalResourceStoreInvariant
import Blotto.RationalUnitLatticeHeight

/-! Deferred source updates use the maintained six-instruction store program.
The retained old-state invariant certifies all operands and selected endpoints.
Logical resource stores and full resource-copy allowances remain distinct. -/

namespace Blotto

def rationalResourceStoreBitCharge {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (copyResources : Bool) : RationalResourceCursor L → ℕ
  | .ready _ => 0
  | .selected state a b _ _ z =>
    PairStoreProgram.updateBitCost model copyResources (⟨state.resource.data, state.resource.size⟩ : PairStoreBuffer n ℚ) a b z

theorem rationalResourceStoreBitCharge_bound {n : ℕ} (L : Fin n → ℚ) (model : RationalCostModel)
    (copyResources : Bool) (D : ℕ) (hD : 0 < D) (hL : ∀ j, OnRationalLattice D (L j))
    (hUnit : ∀ j, L j ≤ 1) (cursor : RationalResourceCursor L)
    (hCursor : rationalResourceStoreInvariant L D cursor) :
    rationalResourceStoreBitCharge model copyResources cursor ≤
      (if copyResources then 2 * n + 30 else 32) * model.rat (8 * binaryWordWidth D + 23) := by
  cases cursor with
  | ready state => exact Nat.zero_le _
  | selected state a b tail he z =>
    rcases hCursor with ⟨hOld, hz⟩
    let p := state.pair a b tail he
    have hZLattice : OnRationalLattice D z := by
      rcases hz with rfl | rfl
      · exact p.lower_on_lattice (hOld.1 a) (hOld.1 b) (hL b)
      · exact p.upper_on_lattice (hOld.1 a) (hOld.1 b) (hL a)
    have hBox := p.branch_feasible hz
    have hZBox : 0 ≤ z ∧ z ≤ 1 := ⟨hBox.1, hBox.2.1.trans (hUnit a)⟩
    have hCells : ∀ j, RationalHeight (state.resource.allocation j) (2 + binaryWordWidth D) :=
      fun j => (rationalHeight_unit_lattice hD (hOld.1 j) (hOld.2 j)).mono (by omega)
    have hZ := (rationalHeight_unit_lattice hD hZLattice hZBox).mono (by omega : binaryWordWidth D ≤ 2 + binaryWordWidth D)
    have h := PairStoreProgram.updateBitCost_bound model copyResources
      (⟨state.resource.data, state.resource.size⟩ : PairStoreBuffer n ℚ) a b z (2 + binaryWordWidth D) (by omega) hCells hZ
    have hWidth : 8 * (2 + binaryWordWidth D) + 7 = 8 * binaryWordWidth D + 23 := by omega
    rw [hWidth] at h
    exact h

end Blotto
