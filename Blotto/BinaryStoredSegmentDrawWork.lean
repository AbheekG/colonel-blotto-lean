import Blotto.BinaryStoredSegmentChoiceWork

/-! The measured stored-segment draw performs native selection once and then
the retained midpoint/interpolation producer only on success. It preserves
exhaustion and absolute reader position. Its primitive work ledger does not
charge evaluating its bookkeeping, metadata or physical compiler execution. -/

namespace Blotto.BinaryStoredSegmentDrawWork
open BinaryRationalNormalization BinaryStoredSegmentChoiceWork

def runIndexedWork {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) : (Option (FixedArrayTable n SignedWord) × ℕ) × ℕ :=
  let selected := selectIndexedWork prepared fallback N bits pos hp
  match selected.1.1 with
  | none => ((none, selected.1.2), selected.2)
  | some slot =>
      let row := BinarySegmentPoint.sampleWithWork prepared.table slot K scalar
      ((some row.1, selected.1.2), selected.2 + row.2)

theorem runIndexedWork_state {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWork prepared fallback K N scalar bits pos hp).1 = prepared.runIndexed fallback K N scalar bits pos hp := by
  unfold runIndexedWork BinaryStoredSegmentProgram.Prepared.runIndexed
  rw [← selectIndexedWork_state prepared fallback N bits pos hp]
  dsimp only
  cases hs : (selectIndexedWork prepared fallback N bits pos hp).1.1 <;> rfl

def pointBound (n s K : ℕ) : ℕ := 180 * (K + 3) ^ 3 +
  9 * n * BinaryRationalExpression.uniformPrice (expressionHeightBudget (max s (K + 2)) 3) +
  2 * n * (3 + 4 * expressionHeightBudget (max s (K + 2)) 3) + n + 4

theorem runIndexedWork_bound {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s t : ℕ) (ht : 2 ≤ t)
    (hWeights : ∀ slot, RationalHeight (source.weight slot) s)
    (hEndpoints : ∀ slot j, RationalHeight (source.P slot j) t ∧ RationalHeight (source.Q slot j) t)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWork prepared fallback K N scalar bits pos hp).2 ≤ selectionBound k s (N - pos) + pointBound n t K := by
  have hSelect := selectIndexedWork_bound prepared source hR s hWeights fallback N bits pos hp
  unfold runIndexedWork
  dsimp only
  cases hs : (selectIndexedWork prepared fallback N bits pos hp).1.1 with
  | none => dsimp only; exact hSelect.trans (Nat.le_add_right _ _)
  | some slot =>
      dsimp only
      have hPoint := BinarySegmentPoint.sampleWork_bound prepared.table source prepared.canonical hR t ht hEndpoints slot K scalar
      exact Nat.add_le_add hSelect hPoint

theorem runIndexedWork_position {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    pos ≤ (runIndexedWork prepared fallback K N scalar bits pos hp).1.2 ∧
      (runIndexedWork prepared fallback K N scalar bits pos hp).1.2 ≤ N := by
  rw [runIndexedWork_state]
  exact BinarySegmentCategorical.selectIndexed_position prepared.table source prepared.canonical hR fallback N bits pos hp

end Blotto.BinaryStoredSegmentDrawWork
