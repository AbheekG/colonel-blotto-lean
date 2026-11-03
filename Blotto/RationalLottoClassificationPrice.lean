import Blotto.RationalFractionalScanCost
import Blotto.RationalLottoStoreBitPrice

/-! The initial array/strict scan and selected two-coordinate retention tests
have linear operand prices on the reached cached source path. Reader, address,
list/control, allocator and ownership work remain separate. -/

namespace Blotto

def rationalResourceRetainedBitCharge {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel) : RationalResourceCursor L → ℕ
  | .ready _ => 0
  | .selected state a b tail he z =>
    rationalRetainedFractionalBitCost model L (state.update a b tail he z).resource a b

theorem rationalResourceRetainedBitCharge_bound {n : ℕ} (L : Fin n → ℚ) (model : RationalCostModel)
    (D : ℕ) (hD : 0 < D) (hL : ∀ j, OnRationalLattice D (L j))
    (hUnit : ∀ j, 0 ≤ L j ∧ L j ≤ 1) (cursor : RationalResourceCursor L)
    (hCursor : rationalResourceStoreInvariant L D cursor) :
    rationalResourceRetainedBitCharge model cursor ≤ 10 * model.rat (3 + 2 * binaryWordWidth D) := by
  have hMat := rationalResourceStoreInvariant_materialize L D hL (fun j => (hUnit j).2) cursor hCursor
  have hCaps := fun j => rationalFractionalWordBound_lattice hD (hL j) (hUnit j)
  have hResources := fun j => rationalFractionalWordBound_lattice hD (hMat.1 j) (hMat.2 j)
  have hZero : rationalWordWidth (0 : ℚ) ≤ 3 + 2 * binaryWordWidth D := by
    have h : rationalWordWidth (0 : ℚ) = 3 := by decide
    omega
  cases cursor with
  | ready state => exact Nat.zero_le _
  | selected state a b tail he z =>
    exact rationalRetainedFractionalBitCost_bound model L (state.update a b tail he z).resource a b _ hZero hCaps hResources

end Blotto
namespace Blotto.RationalLottoResourceSystem

theorem initialDataBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1) (hL : ∀ j, OnRationalLattice D (i.length j))
    (hR : ∀ j, OnRationalLattice D (i.initial j)) :
    rationalInitialDataBitCost model i.length i.initial ≤ 7 * n * model.rat (3 + 2 * binaryWordWidth D) := by
  apply rationalInitialDataBitCost_bound model i.length i.initial
  · have h : rationalWordWidth (0 : ℚ) = 3 := by decide
    omega
  · intro j
    exact rationalFractionalWordBound_lattice hD (hL j) ⟨(i.length_pos j).le, (i.length_le j).trans hB⟩
  · intro j
    exact rationalFractionalWordBound_lattice hD (hR j)
      ⟨(i.initial_box j).1, ((i.initial_box j).2.trans (i.length_le j)).trans hB⟩

def cachedSourceRetainedBitCost {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : ℕ :=
  (i.machine K outerBits scalarBits).runCachedCallbackWork
    (WordStateMachine.serialSourceCharge (fun cursor : i.PhaseCursor => rationalResourceRetainedBitCharge model cursor.1))
    R (i.samplingStart K outerBits scalarBits) choiceBits

theorem cachedSourceRetainedBitCost_initial_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceRetainedBitCost model K R outerBits scalarBits choiceBits ≤
      (10 * model.rat (3 + 2 * binaryWordWidth D)) * i.phase.rank i.start := by
  have h := i.phase.runCachedSerialSourceWork_initial_bound_under
    (fun value => ((i.terminalData value).program K outerBits scalarBits).machine)
    (fun value => ((i.terminalData value).program K outerBits scalarBits).start) 80
    (fun value => ((i.terminalData value).program K outerBits scalarBits).rank_le)
    (fun cursor : i.PhaseCursor => rationalResourceStoreInvariant i.length D cursor.1)
    (i.phase_storeInvariant_closed D hB hL)
    (fun cursor : i.PhaseCursor => rationalResourceRetainedBitCharge model cursor.1)
    (10 * model.rat (3 + 2 * binaryWordWidth D))
    (fun cursor hc => rationalResourceRetainedBitCharge_bound i.length model D hD hL
      (fun j => ⟨(i.length_pos j).le, (i.length_le j).trans hB⟩) cursor.1 hc)
    R i.start (i.phase_storeInvariant_start D hB hR) choiceBits
  change i.cachedSourceRetainedBitCost model K R outerBits scalarBits choiceBits ≤
    (10 * model.rat (3 + 2 * binaryWordWidth D)) * i.phase.rank i.start + 0 at h
  simpa only [Nat.add_zero] using h

theorem cachedSourceRetainedBitCost_bound {n : ℕ} (i : RationalLottoResourceSystem n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hR : ∀ j, OnRationalLattice D (i.initial j))
    (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.cachedSourceRetainedBitCost model K R outerBits scalarBits choiceBits ≤
      10 * (n - 1) * model.rat (3 + 2 * binaryWordWidth D) := by
  have h := i.cachedSourceRetainedBitCost_initial_bound model D hD hB hL hR K R outerBits scalarBits choiceBits
  have hRank := Nat.mul_le_mul_left (10 * model.rat (3 + 2 * binaryWordWidth D)) i.phase_rank
  have hPrice : (10 * model.rat (3 + 2 * binaryWordWidth D)) * (n - 1) =
      10 * (n - 1) * model.rat (3 + 2 * binaryWordWidth D) := by ring
  exact h.trans (hRank.trans_eq hPrice)

end Blotto.RationalLottoResourceSystem
