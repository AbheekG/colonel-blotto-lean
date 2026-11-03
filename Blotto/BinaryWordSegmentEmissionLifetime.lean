import Blotto.BinaryScalarTape
import Blotto.BinaryWordSegmentResultHeight
import Blotto.BinaryGroupEmissionLifetimeBound

/-! The selected native segment row feeds actual cached route emission.
Uniform and mixed pivot paths preserve none, all output words and the entire
Boolean seed cursor. No row/continuation result is supplied by the caller. -/
namespace Blotto.BinaryWordSegmentEmissionLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryStoredSegmentProgram BinaryGroupEmissionLifetime
set_option maxHeartbeats 2000000

def uniformRun {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared m k) (fallback : Fin k)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerSegment.Result store n × Trace :=
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp
  let emitted := emitOptionWithTrace routes drawn.1.1
  ((emitted.1,drawn.1.2),wrap 32 2 [drawn.2,emitted.2])

theorem uniformRun_erasure {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared m k) (fallback : Fin k)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store prepared fallback routes K scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerSegment.run store prepared fallback K scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emit routes),drawn.2) := by
  have hRows := BinaryWordSegmentResultHeight.success_canonical store prepared fallback K scalar pc hp
  unfold uniformRun
  dsimp only
  rw [emitOptionWithTrace_erasure routes _ hRoutes hRows,BinaryWordSegmentLifetime.runWithTrace_erasure]

def mixedRun {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared (m + 1) k) (fallback : Fin k)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerSegment.Result store n × Trace :=
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp
  let emitted := emitMixedOptionWithTrace routes pivot drawn.1.1
  ((emitted.1,drawn.1.2),wrap 32 2 [drawn.2,emitted.2])

theorem mixedRun_erasure {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared (m + 1) k) (fallback : Fin k)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (hRoutes : ∀ j,CanonicalWord (routes.read j).2)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedRun store prepared fallback routes pivot K scalar pc hp).1 =
      let drawn := BinaryPRGWordControllerSegment.run store prepared fallback K scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emitMixed routes pivot),drawn.2) := by
  have hRows := BinaryWordSegmentResultHeight.success_canonical store prepared fallback K scalar pc hp
  unfold mixedRun
  dsimp only
  rw [emitMixedOptionWithTrace_erasure routes pivot _ hRoutes hRows,BinaryWordSegmentLifetime.runWithTrace_erasure]

theorem uniformRun_position {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared m k) (fallback : Fin k)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (uniformRun store prepared fallback routes K scalar pc hp).1.2.value ∧
      (uniformRun store prepared fallback routes K scalar pc hp).1.2.value ≤ store.cap.value :=
  BinaryWordSegmentLifetime.runWithTrace_position store prepared fallback K scalar pc hp

theorem mixedRun_position {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared (m + 1) k) (fallback : Fin k)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (mixedRun store prepared fallback routes pivot K scalar pc hp).1.2.value ∧
      (mixedRun store prepared fallback routes pivot K scalar pc hp).1.2.value ≤ store.cap.value :=
  BinaryWordSegmentLifetime.runWithTrace_position store prepared fallback K scalar pc hp

end Blotto.BinaryWordSegmentEmissionLifetime
