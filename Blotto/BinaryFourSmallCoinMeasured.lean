import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryWordCoinMeasured
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryFourSmallCoinLifetime

/-! Actual measured canonicalization of the original small-root probability
feeds the measured Boolean-PC coin. Full preceding data/trace and absolute
cursor are preserved. Original fields derive source work and retained-prefix
bounds; native observers/references/allocator realization remains separate. -/

namespace Blotto.BinaryFourSmallCoinMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def sampleWithExtras (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ :=
  let produced := BinaryNormalizedCoordinate.canonicalize input.p
  let probability := produced.1
  let sampled := BinaryWordCoinMeasured.sample store probability.1.1 pc hp
  (((sampled.1.1,wrap 32 2 [probability.1.2,sampled.1.2]),probability.2+sampled.2+8),produced.2)

def sample (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ :=
  (sampleWithExtras store input pc hp).1

theorem sampleWithExtras_compat (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (sampleWithExtras store input pc hp).1 = sample store input pc hp := rfl

theorem sample_record (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    sample store input pc hp =
  let probability := BinaryQuadraticMeasured.canonicalize input.p
  let sampled := BinaryWordCoinMeasured.sample store probability.1.1 pc hp
  ((sampled.1.1,wrap 32 2 [probability.1.2,sampled.1.2]),probability.2+sampled.2+8) := by
  simp only [sample,sampleWithExtras,BinaryNormalizedCoordinate.canonicalize_record]

theorem sample_erases (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (sample store input pc hp).1 = BinaryFourSmallCoinLifetime.sampleWithTrace store input pc hp := by
  simp only [sample_record,BinaryFourSmallCoinLifetime.sampleWithTrace,BinaryFourSmallCoinLifetime.probabilityWithTrace,
    BinaryQuadraticMeasured.canonicalize_erases,BinaryWordCoinMeasured.sample_erases]

def workEnvelope (s i remaining : ℕ) : ℕ := 600*(2*s+2)^2+
  BinaryWordCoinMeasured.samplePrice (1+2*s) i remaining+8

theorem sample_work (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (sample store input pc hp).2 ≤ workEnvelope s store.width (store.cap.value-pc.value) := by
  rw [sample_record]
  let probability := BinaryQuadraticMeasured.canonicalize input.p
  have hHeight : RationalHeight (value input.p) s := by rw [hR.2.2.2.2.2]; exact hH.2.2.2.2.2
  have hValid : BinaryRationalOpcode.Valid input.p := hC.2.2.2.2.2.1
  have hInputWidth : width input.p ≤ 1+2*s :=
    (hC.2.2.2.2.2.2).trans (rationalWordWidth_of_height hHeight)
  have hProbability : probability.1.1 = BinaryRationalOpcode.canonicalize input.p := by
    rw [BinaryQuadraticMeasured.canonicalize_erases]
    exact BinaryQuadraticLifetime.canonicalizeWithTrace_state input.p hValid
  have hProbabilityWidth : width probability.1.1 ≤ 1+2*s := by
    rw [hProbability]
    exact (BinaryRationalOpcode.canonicalize_width input.p hValid).trans (rationalWordWidth_of_height hHeight)
  have hNorm := BinaryQuadraticNormalization.canonicalizeWithWork_bound input.p
  rw [← BinaryQuadraticMeasured.canonicalize_work] at hNorm
  have hPower := Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left (show width input.p+1 ≤ 2*s+2 by omega) 2)
  have hCoin := BinaryWordCoinMeasured.sample_work store probability.1.1 pc hp (1+2*s) hProbabilityWidth
  change probability.2 ≤ _ at hNorm
  change probability.2+(BinaryWordCoinMeasured.sample store probability.1.1 pc hp).2+8 ≤ _
  unfold workEnvelope
  omega

theorem sample_position (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (sample store input pc hp).1.1.2.value ∧
      (sample store input pc hp).1.1.2.value ≤ store.cap.value := by
  rw [sample_erases]
  exact BinaryFourSmallCoinLifetime.sampleWithTrace_position store input pc hp

theorem all_prefix (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (sample store input pc hp).1.2 steps ≤ borrowed+
      BinaryFourSmallCoinLifetime.envelope s store.width (store.cap.value-pc.value) ∧
    framePeak ((sample store input pc hp).1.2.take steps) ≤
      BinaryFourSmallCoinLifetime.envelope s store.width (store.cap.value-pc.value) := by
  rw [sample_erases]
  exact BinaryFourSmallCoinLifetime.all_prefix store input source hC hR s hH pc hp borrowed steps

end Blotto.BinaryFourSmallCoinMeasured
