import Blotto.BinaryScalarTape
import Blotto.BinaryWordSegmentLifetimeBound
import Blotto.BinaryCategoricalLowerLifetime

/-! A single retained segment table feeds optional selection/interpolation and,
on exhaustion, deterministic lower selection/interpolation. No factory is
replayed; fallback preserves the actual returned absolute Boolean cursor. -/
namespace Blotto.BinaryWordSegmentFixedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryStoredSegmentProgram
set_option maxHeartbeats 2000000

def lowerWithTrace {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) :
    FixedArrayTable n SignedWord × Trace :=
  let selected := BinaryCategoricalLowerLifetime.segmentWithTrace prepared fallback
  let point := BinaryQuadraticPointLifetime.sampleWithTrace prepared.table selected.1 K scalar
  (point.1,wrap 24 2 [selected.2,point.2])

theorem lowerWithTrace_erasure {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) :
    (lowerWithTrace prepared fallback K scalar).1 = prepared.lowerLeaf fallback K scalar := by
  unfold lowerWithTrace Prepared.lowerLeaf
  dsimp only
  rw [BinaryQuadraticPointLifetime.sampleWithTrace_state _ prepared.canonical,
    BinaryCategoricalLowerLifetime.segmentWithTrace_erasure]

def lowerEnvelope (n k s K : ℕ) : ℕ :=
  BinaryCategoricalLowerLifetime.envelope k s+BinaryQuadraticPointLifetime.bound n s K+
    BinaryQuadraticPointLifetime.frames n s K+64

theorem lowerWithTrace_usage {n k : ℕ} (prepared : Prepared n k) (fallback : Fin k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s) (K : ℕ) (scalar : BinaryScalarTape K) :
    usage (lowerWithTrace prepared fallback K scalar).2 ≤ lowerEnvelope n k s K := by
  let selected := BinaryCategoricalLowerLifetime.segmentWithTrace prepared fallback
  let point := BinaryQuadraticPointLifetime.sampleWithTrace prepared.table selected.1 K scalar
  have hEndpoints : ∀ i j,RationalHeight (value ((prepared.table.P.read i).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read i).read j)) s := by
    intro i j
    rw [hR.2.1 i j,hR.2.2 i j]
    exact hHeight.2 i j
  have hS := BinaryCategoricalLowerLifetime.segmentWithTrace_usage prepared source hR s hHeight.1 fallback
  have hP := BinaryQuadraticPointLifetime.sampleWithTrace_bounds prepared.table prepared.canonical s hs hEndpoints selected.1 K scalar
  have hUsage : usage point.2 ≤ BinaryQuadraticPointLifetime.bound n s K+BinaryQuadraticPointLifetime.frames n s K := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    exact Nat.add_le_add hP.1 hP.2
  have hw := wrap_usage 24 2 [selected.2,point.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (lowerWithTrace prepared fallback K scalar).2 ≤ _ at hw
  change usage selected.2 ≤ _ at hS
  unfold lowerEnvelope
  omega

def runWithTrace {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : (FixedArrayTable n SignedWord × FixedBinaryWord store.width) × Trace :=
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp
  match drawn.1.1 with
  | some row => ((row,drawn.1.2),wrap 24 2 [drawn.2])
  | none =>
      let lower := lowerWithTrace prepared fallback K scalar
      ((lower.1,drawn.1.2),wrap 32 2 [drawn.2,lower.2])

theorem runWithTrace_erasure {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared fallback K scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerSegment.run store prepared fallback K scalar pc hp
      (match drawn.1 with | some row => row | none => prepared.lowerLeaf fallback K scalar,drawn.2) := by
  unfold runWithTrace
  dsimp only
  rw [← BinaryWordSegmentLifetime.runWithTrace_erasure store prepared fallback K scalar pc hp]
  cases (BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp).1.1 with
  | some row => rfl
  | none => exact Prod.ext (lowerWithTrace_erasure prepared fallback K scalar) rfl

theorem runWithTrace_window {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared fallback K scalar pc hp).1.1 =
      prepared.sample fallback K (store.cap.value-pc.value) scalar
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value-pc.value) (by omega)) := by
  have h := congrArg Prod.fst (BinaryPRGWordControllerSegment.run_offset store prepared fallback K scalar
    pc.value (store.cap.value-pc.value) (by omega) _ (by intro index; rfl) pc hp 0 (Nat.zero_le _) (by omega))
  change (BinaryPRGWordControllerSegment.run store prepared fallback K scalar pc hp).1 =
    (prepared.runIndexed fallback K (store.cap.value-pc.value) scalar
      (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
        (store.cap.value-pc.value) (by omega)) 0 (Nat.zero_le _)).1 at h
  rw [runWithTrace_erasure]
  dsimp only
  unfold Prepared.sample
  rw [h]
  rfl

theorem runWithTrace_position {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store prepared fallback K scalar pc hp).1.2.value ∧
      (runWithTrace store prepared fallback K scalar pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerSegment.run_position store prepared fallback K scalar pc hp

theorem runWithTrace_cursor {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared fallback K scalar pc hp).1.2 =
      (BinaryPRGWordControllerSegment.run store prepared fallback K scalar pc hp).2 := by
  rw [runWithTrace_erasure]

def envelope (n k s K i b : ℕ) : ℕ :=
  BinaryWordSegmentLifetimeBound.envelope n k s K i b+lowerEnvelope n k s K+128

theorem runWithTrace_usage {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (fallback : Fin k) (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store prepared fallback K scalar pc hp).2 ≤ envelope n k s K store.width store.cap.value := by
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp
  have hD := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared source hR s hs hHeight.1 hHeight.2
    fallback K scalar pc hp
  have hL := lowerWithTrace_usage prepared fallback source hR s hs hHeight K scalar
  change usage drawn.2 ≤ _ at hD
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [drawn.2]) ≤ _
    unfold envelope
    omega
  · have hw := wrap_usage 32 2 [drawn.2,(lowerWithTrace prepared fallback K scalar).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [drawn.2,(lowerWithTrace prepared fallback K scalar).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (fallback : Fin k) (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store prepared fallback K scalar pc hp).2 steps ≤
      borrowed+envelope n k s K store.width store.cap.value ∧
      framePeak ((runWithTrace store prepared fallback K scalar pc hp).2.take steps) ≤ envelope n k s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store prepared fallback source hR s hs hHeight K scalar pc hp) borrowed steps

end Blotto.BinaryWordSegmentFixedLifetime
