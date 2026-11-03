import Blotto.BinaryFourGluingDrawLifetime
import Blotto.BinaryWordCoinLifetime

/-! Actual canonicalization of the original small-root probability followed by
its Boolean-PC word coin. The probability and seed cursor are consumed once. -/
namespace Blotto.BinaryFourSmallCoinLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def probabilityWithTrace (input : BinaryFourParameters.Input) : SignedWord × Trace :=
  BinaryQuadraticLifetime.canonicalizeWithTrace input.p

theorem probabilityWithTrace_erasure (input : BinaryFourParameters.Input) :
    (probabilityWithTrace input).1 = BinaryPRGWordControllerFour.probability input := by
  exact BinaryQuadraticLifetime.canonicalizeWithTrace_erases input.p

def sampleWithTrace (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (Option Bool × FixedBinaryWord store.width) × Trace :=
  let probability := probabilityWithTrace input
  let sampled := BinaryWordCoinLifetime.sampleWithTrace store probability.1 pc hp
  (sampled.1,wrap 32 2 [probability.2,sampled.2])

theorem sampleWithTrace_erasure (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (sampleWithTrace store input pc hp).1 =
      BinaryPRGWordControllerDataCoin.sample store (BinaryPRGWordControllerFour.probability input) pc hp := by
  unfold sampleWithTrace
  dsimp only
  rw [BinaryWordCoinLifetime.sampleWithTrace_erases,probabilityWithTrace_erasure]

theorem sampleWithTrace_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (sampleWithTrace store input pc hp).1.2.value ∧
      (sampleWithTrace store input pc hp).1.2.value ≤ store.cap.value := by
  rw [sampleWithTrace_erasure]
  exact BinaryPRGWordControllerDataCoin.sample_position store _ pc hp

def envelope (s indexWidth remaining : ℕ) : ℕ :=
  3000 * (2*s+3)^3 + (6*(2*s+1)+28) +
    BinaryWordCoinLifetime.sampleBound (1+2*s) indexWidth remaining +
    (remaining+2*(1+2*s)+2*indexWidth+24) + 80

theorem sampleWithTrace_usage (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (s : ℕ) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (sampleWithTrace store input pc hp).2 ≤
      envelope s store.width (store.cap.value-pc.value) := by
  let probability := probabilityWithTrace input
  let sampled := BinaryWordCoinLifetime.sampleWithTrace store probability.1 pc hp
  have hHeight : RationalHeight (value input.p) s := by
    rw [hR.2.2.2.2.2]
    exact hH.2.2.2.2.2
  have hValid : BinaryRationalOpcode.Valid input.p := hC.2.2.2.2.2.1
  have hInputWidth : width input.p ≤ 1+2*s :=
    (hC.2.2.2.2.2.2).trans (rationalWordWidth_of_height hHeight)
  have hProbability : probability.1 = BinaryRationalOpcode.canonicalize input.p :=
    BinaryQuadraticLifetime.canonicalizeWithTrace_state input.p hValid
  have hProbabilityWidth : width probability.1 ≤ 1+2*s := by
    rw [hProbability]
    exact (BinaryRationalOpcode.canonicalize_width input.p hValid).trans
      (rationalWordWidth_of_height hHeight)
  have hNorm := BinaryQuadraticLifetime.canonicalizeWithTrace_bounds input.p
  have hCoin := BinaryWordCoinLifetime.sampleWithTrace_bounds store probability.1 pc hp (1+2*s) hProbabilityWidth
  have hNormUsage : usage probability.2 ≤ 3000*(2*s+3)^3 + (6*(2*s+1)+28) := by
    change usage (BinaryQuadraticLifetime.canonicalizeWithTrace input.p).2 ≤ _
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    have hPow : (width input.p+2)^3 ≤ (2*s+3)^3 :=
      (Nat.pow_le_pow_left (by omega : width input.p+2 ≤ 2*s+3)) 3
    nlinarith only [hNorm.1,hNorm.2,hInputWidth,hPow]
  have hCoinUsage : usage sampled.2 ≤
      BinaryWordCoinLifetime.sampleBound (1+2*s) store.width (store.cap.value-pc.value) +
        (store.cap.value-pc.value+2*(1+2*s)+2*store.width+24) := by
    have hCells := hCoin.1
    have hFrames := hCoin.2
    change listCells sampled.2 + arraySlots sampled.2 ≤ _ at hCells
    change framePeak sampled.2 ≤ _ at hFrames
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hw := wrap_usage 32 2 [probability.2,sampled.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [probability.2,sampled.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (s : ℕ) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (sampleWithTrace store input pc hp).2 steps ≤
      borrowed + envelope s store.width (store.cap.value-pc.value) ∧
    framePeak ((sampleWithTrace store input pc hp).2.take steps) ≤
      envelope s store.width (store.cap.value-pc.value) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (sampleWithTrace_usage store input source hC hR s hH pc hp) borrowed steps

end Blotto.BinaryFourSmallCoinLifetime
