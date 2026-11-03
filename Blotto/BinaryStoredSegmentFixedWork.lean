import Blotto.BinaryCategoricalLowerLeafWork
import Blotto.BinaryStoredSegmentDrawWork

/-! A native stored-segment fixed draw joins indexed selection, interpolation
and the exact syntactic lower-leaf exhaustion fallback. The original fallback
is priced by actual preparations, including zero slots. The ledger is primitive
work; bookkeeping, addressing, ownership and compiler costs remain separate. -/

namespace Blotto.BinaryStoredSegmentFixedWork
open BinaryRationalNormalization BinaryStoredSegmentChoiceWork BinaryStoredSegmentDrawWork

def fallbackWithWork {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool) : FixedArrayTable n SignedWord × ℕ :=
  let chosen := BinaryCategoricalLowerLeafWork.segmentWithWork prepared fallback
  let row := BinarySegmentPoint.sampleWithWork prepared.table chosen.1 K scalar
  (row.1, chosen.2 + row.2)

theorem fallbackWithWork_state {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool) :
    (fallbackWithWork prepared fallback K scalar).1 = prepared.lowerLeaf fallback K scalar := by
  unfold fallbackWithWork BinaryStoredSegmentProgram.Prepared.lowerLeaf
  dsimp only
  rw [BinarySegmentPoint.sampleWithWork_state, BinaryCategoricalLowerLeafWork.segmentWithWork_state]

theorem fallbackWithWork_bound {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s t : ℕ) (ht : 2 ≤ t)
    (hWeights : ∀ slot, RationalHeight (source.weight slot) s)
    (hEndpoints : ∀ slot j, RationalHeight (source.P slot j) t ∧ RationalHeight (source.Q slot j) t)
    (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool) :
    (fallbackWithWork prepared fallback K scalar).2 ≤ BinaryCategoricalLowerLeafWork.bound k s + pointBound n t K :=
  Nat.add_le_add (BinaryCategoricalLowerLeafWork.segmentWithWork_bound prepared source hR s hWeights fallback)
    (BinarySegmentPoint.sampleWork_bound prepared.table source prepared.canonical hR t ht hEndpoints _ K scalar)

def sampleWithWork {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable n SignedWord × ℕ :=
  let reached := runIndexedWork prepared fallback K N scalar bits 0 (Nat.zero_le N)
  match reached.1.1 with
  | some row => (row, reached.2)
  | none =>
      let row := fallbackWithWork prepared fallback K scalar
      (row.1, reached.2 + row.2)

theorem sampleWithWork_state {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (sampleWithWork prepared fallback K N scalar bits).1 = prepared.sample fallback K N scalar bits := by
  unfold sampleWithWork BinaryStoredSegmentProgram.Prepared.sample
  rw [← runIndexedWork_state prepared fallback K N scalar bits 0 (Nat.zero_le N)]
  dsimp only
  cases hs : (runIndexedWork prepared fallback K N scalar bits 0 (Nat.zero_le N)).1.1 with
  | none => exact fallbackWithWork_state prepared fallback K scalar
  | some row => rfl

def bound (n k s t K N : ℕ) : ℕ := selectionBound k s N + BinaryCategoricalLowerLeafWork.bound k s + 2 * pointBound n t K

theorem sampleWithWork_bound {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s t : ℕ) (ht : 2 ≤ t)
    (hWeights : ∀ slot, RationalHeight (source.weight slot) s)
    (hEndpoints : ∀ slot j, RationalHeight (source.P slot j) t ∧ RationalHeight (source.Q slot j) t)
    (fallback : Fin k) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (sampleWithWork prepared fallback K N scalar bits).2 ≤ bound n k s t K N := by
  have hRun := runIndexedWork_bound prepared source hR s t ht hWeights hEndpoints fallback K N scalar bits 0 (Nat.zero_le N)
  simp only [Nat.sub_zero] at hRun
  have hFallback := fallbackWithWork_bound prepared source hR s t ht hWeights hEndpoints fallback K scalar
  unfold sampleWithWork
  dsimp only
  cases hs : (runIndexedWork prepared fallback K N scalar bits 0 (Nat.zero_le N)).1.1 <;>
    dsimp only <;> unfold bound <;> omega

end Blotto.BinaryStoredSegmentFixedWork
