import Blotto.BinaryScalarTape
import Blotto.BinaryWordCategoricalLifetimeBound
import Blotto.BinaryQuadraticPointLifetime

/-! A complete retained segment draw consumes the actual Boolean-PC selector
and actual traced direct-midpoint/quadratic interpolation. Weight-list copies,
selected point and cursor are exact, including seed exhaustion. -/
namespace Blotto.BinaryWordSegmentLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredSegmentProgram BinaryStoredSegmentChoiceWork
set_option maxHeartbeats 2000000

def selectWithTrace {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (Option (Fin k) × FixedBinaryWord store.width) × Trace :=
  let selected := BinaryWordCategoricalLifetime.runWithTrace store fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  (selected.1,wrapList k (8 * k + 16) (k + 4) [selected.2])

theorem selectWithTrace_erasure {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (selectWithTrace store prepared fallback pc hp).1 = BinaryPRGWordControllerDataCategorical.run store fallback
      (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp :=
  BinaryWordCategoricalLifetime.runWithTrace_erasure _ _ _ _ _

def runWithTrace {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerSegment.Result store n × Trace :=
  let selected := selectWithTrace store prepared fallback pc hp
  match selected.1.1 with
  | none => ((none,selected.1.2),wrap 16 2 [selected.2])
  | some slot =>
      let point := BinaryQuadraticPointLifetime.sampleWithTrace prepared.table slot K scalar
      ((some point.1,selected.1.2),wrap 24 2 [selected.2,point.2])

theorem runWithTrace_erasure {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store prepared fallback K scalar pc hp).1 = BinaryPRGWordControllerSegment.run store prepared fallback K scalar pc hp := by
  unfold runWithTrace BinaryPRGWordControllerSegment.run
  dsimp only
  rw [← selectWithTrace_erasure]
  cases (selectWithTrace store prepared fallback pc hp).1.1 <;>
    simp only [BinaryQuadraticPointLifetime.sampleWithTrace_erases,BinaryQuadraticPointLifetime.pointData_controller] <;> rfl

theorem runWithTrace_position {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store prepared fallback K scalar pc hp).1.2.value ∧
      (runWithTrace store prepared fallback K scalar pc hp).1.2.value ≤ store.cap.value := by
  have h := BinaryWordCategoricalLifetime.runWithTrace_position store fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  unfold runWithTrace
  dsimp only
  cases (selectWithTrace store prepared fallback pc hp).1.1 <;> exact h

end Blotto.BinaryWordSegmentLifetime
