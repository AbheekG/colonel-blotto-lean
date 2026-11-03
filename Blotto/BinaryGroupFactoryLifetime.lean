import Blotto.BinaryUnorderedThreeLifetime
import Blotto.BinaryUniformPairLifetime
import Blotto.BinaryGroupRetainedPrimitiveRun

/-! Actual cached uniform-two/uniform-three and mixed-two inputs produce the
complete traced descriptor and retained sampler record. All ordering and
regular/exceptional regimes are included. Source validity is proof-only. -/
namespace Blotto.BinaryGroupFactoryLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

def uniformFactory {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    BinaryStoredOverlapEnvironment.Segment m 9 × Trace := by
  by_cases h2 : m = 2
  · subst m
    let made := BinaryUniformPairLifetime.descriptorWithTrace input
    exact (made.1,wrap 64 4 [made.2])
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    let made := BinaryUnorderedThreeLifetime.descriptorWithTrace (uniformThree input)
    exact (made.1,wrap 64 4 [made.2])

theorem uniformFactory_erasure {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hm : m = 2 ∨ m = 3) :
    (uniformFactory input hm).1 = uniformLottery input hm := by
  rcases hm with rfl | rfl
  · exact BinaryUniformPairLifetime.descriptorWithTrace_erasure input
  · exact BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure (uniformThree input) (uniformThree_canonical input hC)

def uniformEnvelope (s : ℕ) : ℕ := BinaryUnorderedThreeLifetime.envelope s + 4096 + 96

theorem uniformFactory_usage {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hm : m = 2 ∨ m = 3)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s) : usage (uniformFactory input hm).2 ≤ uniformEnvelope s := by
  rcases hm with rfl | rfl
  · have h := BinaryUniformPairLifetime.descriptorWithTrace_usage input
    have hw := wrap_usage 64 4 [(BinaryUniformPairLifetime.descriptorWithTrace input).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 64 4 [(BinaryUniformPairLifetime.descriptorWithTrace input).2]) ≤ _
    unfold uniformEnvelope
    omega
  · have h := BinaryUnorderedThreeLifetime.descriptorWithTrace_usage (uniformThree input) (uniformThree_canonical input hC) s hs
      (uniformThree_heights input s hHeight (by omega))
    have hw := wrap_usage 64 4 [(BinaryUnorderedThreeLifetime.descriptorWithTrace (uniformThree input)).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 64 4 [(BinaryUnorderedThreeLifetime.descriptorWithTrace (uniformThree input)).2]) ≤ _
    unfold uniformEnvelope
    omega

def uniformPreparedWithTrace {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) : BinaryStoredSegmentProgram.Prepared m 9 × Trace :=
  let factory := uniformFactory input hm
  have hTable := uniformFactory_erasure input hC hm
  (⟨factory.1,(by rw [hTable]; exact uniformLottery_canonical input hC hm),
    (by rw [hTable]; exact (uniformPrepared input hC hAd hm).nonnegative)⟩,wrap 16 2 [factory.2])

theorem uniformPreparedWithTrace_erasure {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) :
    (uniformPreparedWithTrace input hC hAd hm).1 = uniformPrepared input hC hAd hm := by
  unfold uniformPreparedWithTrace uniformPrepared
  simp only [uniformFactory_erasure input hC hm]

theorem uniformPreparedWithTrace_usage {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s) :
    usage (uniformPreparedWithTrace input hC hAd hm).2 ≤ uniformEnvelope s + 20 := by
  have h := uniformFactory_usage input hC hm s hs hHeight
  have hw := wrap_usage 16 2 [(uniformFactory input hm).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  exact hw.trans (by omega)

def mixedTwoPreparedWithTrace (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    BinaryStoredSegmentProgram.Prepared 3 9 × Trace :=
  let factory := BinaryUnorderedThreeLifetime.descriptorWithTrace (mixedThree input)
  have hTable := BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure (mixedThree input) (mixedThree_canonical input hC)
  (⟨factory.1,(by rw [hTable]; exact BinaryThreeSpecCompiler.descriptor_canonical _ (mixedThree_canonical input hC)),
    (by rw [hTable]; exact (mixedTwoPrepared input hC hAd).nonnegative)⟩,wrap 64 4 [factory.2])

theorem mixedTwoPreparedWithTrace_erasure (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    (mixedTwoPreparedWithTrace input hC hAd).1 = mixedTwoPrepared input hC hAd := by
  unfold mixedTwoPreparedWithTrace mixedTwoPrepared
  simp only [BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure _ (mixedThree_canonical input hC)]

def mixedEnvelope (s : ℕ) : ℕ := BinaryUnorderedThreeLifetime.envelope s + 96

theorem mixedTwoPreparedWithTrace_usage (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input)
    (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s) :
    usage (mixedTwoPreparedWithTrace input hC hAd).2 ≤ mixedEnvelope s := by
  have h := BinaryUnorderedThreeLifetime.descriptorWithTrace_usage (mixedThree input) (mixedThree_canonical input hC) s hs
    (mixedThree_heights input s hHeight)
  have hw := wrap_usage 64 4 [(BinaryUnorderedThreeLifetime.descriptorWithTrace (mixedThree input)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 64 4 [(BinaryUnorderedThreeLifetime.descriptorWithTrace (mixedThree input)).2]) ≤ _
  unfold mixedEnvelope
  omega

end Blotto.BinaryGroupFactoryLifetime
