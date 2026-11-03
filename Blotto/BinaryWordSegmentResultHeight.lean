import Blotto.BinaryScalarTape
import Blotto.BinaryWordSegmentLifetimeBound

/-! Actual successful Boolean-PC segment rows inherit canonical bytes and
heights from the original table endpoints and direct scalar, without a
supplied reached-row or interpreter-execution certificate. -/
namespace Blotto.BinaryWordSegmentResultHeight
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredSegmentProgram
set_option maxHeartbeats 1500000

theorem success_shape {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (row : FixedArrayTable n SignedWord)
    (h : (BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp).1.1 = some row) :
    ∃ slot,row = BinarySegmentPoint.sample prepared.table slot K scalar := by
  rw [BinaryWordSegmentLifetime.runWithTrace_erasure] at h
  unfold BinaryPRGWordControllerSegment.run at h
  obtain ⟨slot,hSlot,hRow⟩ := Option.map_eq_some_iff.mp h
  exact ⟨slot,hRow.symm.trans (BinaryPRGWordControllerSegment.point_state prepared.table prepared.canonical slot K scalar)⟩

theorem success_canonical {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (row : FixedArrayTable n SignedWord)
    (h : (BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp).1.1 = some row) :
    ∀ j,CanonicalWord (row.read j) := by
  obtain ⟨slot,rfl⟩ := success_shape store prepared fallback K scalar pc hp row h
  exact BinarySegmentPoint.sample_canonical prepared.table slot K scalar prepared.canonical

def rowHeight (s K : ℕ) : ℕ := expressionHeightBudget (max s (K + 2)) 3

theorem rowHeight_ge (s K : ℕ) : s ≤ rowHeight s K :=
  (le_max_left _ _).trans (expressionHeightBudget_ge_input _ _)

theorem sample_height {n k : ℕ} (prepared : Prepared n k) (slot : Fin k) (s : ℕ) (hs : 2 ≤ s)
    (hEndpoints : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s) (K : ℕ) (scalar : BinaryScalarTape K) :
    ∀ j,RationalHeight (value ((BinarySegmentPoint.sample prepared.table slot K scalar).read j)) (rowHeight s K) := by
  intro j
  have ht : RationalHeight (value (BinaryDyadicMidpoint.sample K scalar)) (max s (K + 2)) := by
    rw [BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K scalar).mono (le_max_right _ _)
  simp only [BinarySegmentPoint.sample,BinarySegmentPoint.atScalar,FixedArrayTable.read_ofFn]
  rw [BinarySegmentPoint.interpolate_value _ _ _ (prepared.canonical.2.1 slot j)
    (prepared.canonical.2.2 slot j) (BinaryDyadicMidpoint.sample_canonical K scalar)]
  exact RationalInterpolationCode.output_height _ _ _ (max s (K + 2)) (hs.trans (le_max_left _ _))
    ((hEndpoints slot j).1.mono (le_max_left _ _)) ((hEndpoints slot j).2.mono (le_max_left _ _)) ht

theorem success_height {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (s : ℕ) (hs : 2 ≤ s) (hEndpoints : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (row : FixedArrayTable n SignedWord)
    (h : (BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp).1.1 = some row) :
    ∀ j,RationalHeight (value (row.read j)) (rowHeight s K) := by
  obtain ⟨slot,rfl⟩ := success_shape store prepared fallback K scalar pc hp row h
  exact sample_height prepared slot s hs hEndpoints K scalar

end Blotto.BinaryWordSegmentResultHeight
