import Blotto.BinaryScalarTape
import Blotto.BinaryReflectedEmissionLifetime
import Blotto.BinaryPRGWordControllerReflected

/-! One retained terminal table feeds the shared-cap Boolean-PC selector and
selected reflected emission. Both selection exhaustion and the absolute cursor
are preserved, with source-derived every-prefix reservations. -/
namespace Blotto.BinaryReflectedTableDrawLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryReflectedFourSetup
set_option maxHeartbeats 2000000

def oldRun (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerReflected.Result store :=
  let chosen := BinaryPRGWordControllerDataCategorical.run store (0 : Fin 18)
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  (chosen.1.map (fun slot => reflect input (BinarySegmentPoint.sample prepared.table slot K scalar)),chosen.2)

def runWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerReflected.Result store × Trace :=
  let chosen := BinaryWordSegmentLifetime.selectWithTrace store prepared (0 : Fin 18) pc hp
  match chosen.1.1 with
  | none => ((none,chosen.1.2),wrap 24 2 [chosen.2])
  | some slot =>
      let emitted := BinaryReflectedEmissionLifetime.sampleWithTrace input prepared.table slot K scalar
      ((some emitted.1,chosen.1.2),wrap 32 2 [chosen.2,emitted.2])

theorem runWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (prepared : BinaryStoredSegmentProgram.Prepared 3 18)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store input prepared K scalar pc hp).1 = oldRun store input prepared K scalar pc hp := by
  unfold runWithTrace oldRun
  dsimp only
  rw [← BinaryWordSegmentLifetime.selectWithTrace_erasure]
  cases h : (BinaryWordSegmentLifetime.selectWithTrace store prepared (0 : Fin 18) pc hp).1.1 with
  | none => rfl
  | some slot =>
      simp only [BinaryReflectedEmissionLifetime.sampleWithTrace_erasure input hC _ prepared.canonical]
      rfl

theorem runWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store input prepared K scalar pc hp).1.2.value ∧
      (runWithTrace store input prepared K scalar pc hp).1.2.value ≤ store.cap.value := by
  have h := BinaryWordCategoricalLifetime.runWithTrace_position store (0 : Fin 18)
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  unfold runWithTrace
  dsimp only
  cases (BinaryWordSegmentLifetime.selectWithTrace store prepared (0 : Fin 18) pc hp).1.1 <;> exact h

def envelope (s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryWordSegmentLifetimeBound.selectionEnvelope 18 s indexWidth seedCap +
    BinaryReflectedEmissionLifetime.envelope s K + 128

theorem runWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (prepared : BinaryStoredSegmentProgram.Prepared 3 18)
    (source : RationalSegmentLottery 3 18) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (runWithTrace store input prepared K scalar pc hp).2 ≤ envelope s K store.width store.cap.value := by
  let chosen := BinaryWordSegmentLifetime.selectWithTrace store prepared (0 : Fin 18) pc hp
  have hChosen := BinaryWordSegmentLifetimeBound.selectWithTrace_usage store prepared source hR
    s hHeight.1 (0 : Fin 18) pc hp
  change usage chosen.2 ≤ _ at hChosen
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [chosen.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [chosen.2]) ≤ _
    unfold envelope
    omega
  · rename_i slot hSlot
    have hEmitted := BinaryReflectedEmissionLifetime.sampleWithTrace_usage input hC prepared.table
      prepared.canonical source hR s hs hHeight hLengths slot K scalar
    have hw := wrap_usage 32 2 [chosen.2,
      (BinaryReflectedEmissionLifetime.sampleWithTrace input prepared.table slot K scalar).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [chosen.2,
      (BinaryReflectedEmissionLifetime.sampleWithTrace input prepared.table slot K scalar).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (prepared : BinaryStoredSegmentProgram.Prepared 3 18)
    (source : RationalSegmentLottery 3 18) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : source.HeightAt s)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store input prepared K scalar pc hp).2 steps ≤
      borrowed + envelope s K store.width store.cap.value ∧
    framePeak ((runWithTrace store input prepared K scalar pc hp).2.take steps) ≤ envelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store input hC prepared source hR s hs hHeight hLengths K scalar pc hp) borrowed steps

end Blotto.BinaryReflectedTableDrawLifetime
