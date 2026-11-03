import Blotto.BinaryScalarTape
import Blotto.BinaryWordSegmentLifetime

/-! Original normalized segment weights and endpoint heights derive all
selection and interpolation allocation prices, including both failure paths.
The common denominator is proof-only and never a sampler runtime argument. -/
namespace Blotto.BinaryWordSegmentLifetimeBound
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredSegmentProgram BinaryStoredSegmentChoiceWork BinaryWordSegmentLifetime
set_option maxHeartbeats 2000000

def sourceStepEnvelope (k s indexWidth seedCap : ℕ) : ℕ :=
  let b := 1 + k * s
  (k + 1) * (BinaryQuadraticLifetime.opcodeBound (1 + 2 * b) + 8) +
    2500 * (2 + 2 * b)^3 + 32 + k +
    (BinaryQuadraticLifetime.opcodeFrames (1 + 2 * b) + 150 * (2 + 2 * b)^2 + 32) + 4 +
    BinaryWordCategoricalLifetimeBound.coinEnvelope (5 + 8 * b) indexWidth seedCap + 64

theorem step_source (D k s indexWidth seedCap : ℕ) (hWidth : binaryWordWidth D ≤ 1 + k * s) :
    BinaryWordCategoricalLifetimeBound.stepEnvelope D k indexWidth seedCap ≤ sourceStepEnvelope k s indexWidth seedCap := by
  unfold BinaryWordCategoricalLifetimeBound.stepEnvelope BinaryWordCategoricalLifetimeBound.preparationEnvelope
    BinaryQuadraticCategoricalLifetime.preparationBound BinaryQuadraticCategoricalLifetime.sumStepBound
    BinaryQuadraticCategoricalLifetime.arithmeticFrames BinaryQuadraticCategoricalLifetime.operandWidth
    BinaryQuadraticLifetime.opcodeBound BinaryQuadraticLifetime.opcodeFrames
    BinaryWordCategoricalLifetimeBound.coinEnvelope BinaryWordCoinLifetime.sampleBound BinaryWordCoinLifetime.localBound
    sourceStepEnvelope
  unfold BinaryQuadraticLifetime.opcodeBound BinaryQuadraticLifetime.opcodeFrames
    BinaryWordCategoricalLifetimeBound.coinEnvelope BinaryWordCoinLifetime.sampleBound BinaryWordCoinLifetime.localBound
  dsimp only
  gcongr

def selectionEnvelope (k s indexWidth seedCap : ℕ) : ℕ :=
  (k + 1) * sourceStepEnvelope k s indexWidth seedCap + 10 * k + 32

theorem selectWithTrace_usage {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s)
    (fallback : Fin k) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (selectWithTrace store prepared fallback pc hp).2 ≤ selectionEnvelope k s store.width store.cap.value := by
  have hWidth := denominator_width prepared.table s (fun slot => by rw [hR.1 slot]; exact hHeight slot)
  have hUnit := source_unit prepared source hR
  have hLength : (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative).items.length = k := List.length_ofFn
  have hCat := BinaryWordCategoricalLifetimeBound.runWithTrace_usage (denominator prepared.table)
    (denominator_positive prepared.table) k store fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) hUnit (by rw [hLength]) pc hp
  rw [hLength] at hCat
  have hStep := Nat.mul_le_mul_left (k + 1) (step_source (denominator prepared.table) k s store.width store.cap.value hWidth)
  have hw := wrapList_usage k (8 * k + 16) (k + 4)
    [(BinaryWordCategoricalLifetime.runWithTrace store fallback
      (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (selectWithTrace store prepared fallback pc hp).2 ≤ _ at hw
  unfold selectionEnvelope
  omega

def envelope (n k s K indexWidth seedCap : ℕ) : ℕ :=
  selectionEnvelope k s indexWidth seedCap + BinaryQuadraticPointLifetime.bound n s K +
    BinaryQuadraticPointLifetime.frames n s K + 64

theorem runWithTrace_usage {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoint : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp).2 ≤ envelope n k s K store.width store.cap.value := by
  have hSelect := selectWithTrace_usage store prepared source hR s hWeight fallback pc hp
  have hTable : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s := by
    intro slot j
    rw [hR.2.1 slot j,hR.2.2 slot j]
    exact hEndpoint slot j
  unfold BinaryWordSegmentLifetime.runWithTrace
  dsimp only
  cases hSelected : (selectWithTrace store prepared fallback pc hp).1.1 with
  | none =>
      have hw := wrap_usage 16 2 [(selectWithTrace store prepared fallback pc hp).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      unfold envelope
      omega
  | some slot =>
      have hPoint := BinaryQuadraticPointLifetime.sampleWithTrace_bounds prepared.table prepared.canonical s hs hTable slot K scalar
      have hUsage : usage (BinaryQuadraticPointLifetime.sampleWithTrace prepared.table slot K scalar).2 ≤
          BinaryQuadraticPointLifetime.bound n s K + BinaryQuadraticPointLifetime.frames n s K := by
        unfold usage BinaryPRGHeapPrimitiveLifetime.cells
        omega
      have hw := wrap_usage 24 2 [(selectWithTrace store prepared fallback pc hp).2,
        (BinaryQuadraticPointLifetime.sampleWithTrace prepared.table slot K scalar).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      unfold envelope
      omega

theorem all_prefix {n k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hs : 3 ≤ s) (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoint : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (fallback : Fin k) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp).2 steps ≤
        borrowed + envelope n k s K store.width store.cap.value ∧
      framePeak ((BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp).2.take steps) ≤
        envelope n k s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage store prepared source hR s hs hWeight hEndpoint fallback K scalar pc hp) borrowed steps

end Blotto.BinaryWordSegmentLifetimeBound
