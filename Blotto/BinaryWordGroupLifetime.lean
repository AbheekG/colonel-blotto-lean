import Blotto.BinaryScalarTape
import Blotto.BinaryGroupFactoryLifetime
import Blotto.BinaryWordSegmentLifetimeBound
import Blotto.BinaryGroupReachedHeight
import Blotto.BinaryPRGWordControllerTerminal

/-! Complete actual uniform-two/uniform-three and mixed-two group draws.
Their produced descriptor is retained by the Boolean-PC categorical/point
runner. Original group fields derive every factory and draw allocation price. -/
namespace Blotto.BinaryWordGroupLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

def uniformRun {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerTerminal.Result store m × Trace :=
  let prepared := BinaryGroupFactoryLifetime.uniformPreparedWithTrace input hC hAd hm
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp
  (drawn.1,wrap 32 2 [prepared.2,drawn.2])

theorem uniformRun_erasure {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm K scalar pc hp).1 = BinaryPRGWordControllerTerminal.uniformRun store input hC hAd hm K scalar pc hp := by
  unfold uniformRun BinaryPRGWordControllerTerminal.uniformRun
  dsimp only
  rw [BinaryWordSegmentLifetime.runWithTrace_erasure,BinaryGroupFactoryLifetime.uniformPreparedWithTrace_erasure]

def mixedTwoRun (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : BinaryPRGWordControllerTerminal.Result store 3 × Trace :=
  let prepared := BinaryGroupFactoryLifetime.mixedTwoPreparedWithTrace input hC hAd
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp
  (drawn.1,wrap 32 2 [prepared.2,drawn.2])

theorem mixedTwoRun_erasure (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd K scalar pc hp).1 =
      BinaryPRGWordControllerSegment.run store (mixedTwoPrepared input hC hAd) 0 K scalar pc hp := by
  unfold mixedTwoRun
  dsimp only
  rw [BinaryWordSegmentLifetime.runWithTrace_erasure,BinaryGroupFactoryLifetime.mixedTwoPreparedWithTrace_erasure]

def uniformEnvelope (m s K indexWidth seedCap : ℕ) : ℕ := BinaryGroupFactoryLifetime.uniformEnvelope s + 20 +
  BinaryWordSegmentLifetimeBound.envelope m 9 (expressionHeightBudget s 18) K indexWidth seedCap + 64

def mixedEnvelope (s K indexWidth seedCap : ℕ) : ℕ := BinaryGroupFactoryLifetime.mixedEnvelope s +
  BinaryWordSegmentLifetimeBound.envelope 3 9 (expressionHeightBudget s 18) K indexWidth seedCap + 64

theorem uniformRun_usage {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (uniformRun store input hC hAd hm K scalar pc hp).2 ≤ uniformEnvelope m s K store.width store.cap.value := by
  obtain ⟨source,hRef⟩ := hAd
  let prepared := BinaryGroupFactoryLifetime.uniformPreparedWithTrace input hC ⟨source,hRef⟩ hm
  have hE := BinaryGroupFactoryLifetime.uniformPreparedWithTrace_erasure input hC ⟨source,hRef⟩ hm
  have hR : prepared.1.table.Refines (source.lottery hm) := by
    dsimp only [prepared]
    rw [hE]
    exact uniformLottery_refines input source hC hRef hm
  have hTable := BinaryGroupRetainedPrimitiveRun.uniformLottery_height input hC hm s hs hHeight
  have hWeight : ∀ slot,RationalHeight ((source.lottery hm).weight slot) (expressionHeightBudget s 18) := by
    intro slot
    rw [← hR.1 slot]
    dsimp only [prepared]
    rw [hE]
    exact hTable.1 slot
  have hEndpoints : ∀ slot j,RationalHeight ((source.lottery hm).P slot j) (expressionHeightBudget s 18) ∧
      RationalHeight ((source.lottery hm).Q slot j) (expressionHeightBudget s 18) := by
    intro slot j
    rw [← hR.2.1 slot j,← hR.2.2 slot j]
    dsimp only [prepared]
    rw [hE]
    exact hTable.2 slot j
  have hFactory := BinaryGroupFactoryLifetime.uniformPreparedWithTrace_usage input hC ⟨source,hRef⟩ hm s hs hHeight
  have hDraw := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared.1 (source.lottery hm) hR
    (expressionHeightBudget s 18) (hs.trans (expressionHeightBudget_ge_input s 18)) hWeight hEndpoints 0 K scalar pc hp
  have hw := wrap_usage 32 2 [prepared.2,(BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.2,(BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp).2]) ≤ _
  change usage prepared.2 ≤ _ at hFactory
  unfold uniformEnvelope
  omega

theorem mixedTwoRun_usage (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (mixedTwoRun store input hC hAd K scalar pc hp).2 ≤ mixedEnvelope s K store.width store.cap.value := by
  obtain ⟨source,hRef⟩ := hAd
  let prepared := BinaryGroupFactoryLifetime.mixedTwoPreparedWithTrace input hC ⟨source,hRef⟩
  have hE := BinaryGroupFactoryLifetime.mixedTwoPreparedWithTrace_erasure input hC ⟨source,hRef⟩
  have hR : prepared.1.table.Refines source.threeInput.segmentLottery := by
    dsimp only [prepared]
    rw [hE]
    exact BinaryThreeSpecCompiler.descriptor_refines _ _ (mixedThree_canonical input hC) (mixedThree_refines input source hRef)
  have hTable := BinaryUnorderedThreeFactoryWork.descriptor_height _ (mixedThree_canonical input hC) s hs
    (mixedThree_heights input s hHeight)
  have hWeight : ∀ slot,RationalHeight (source.threeInput.segmentLottery.weight slot) (expressionHeightBudget s 18) := by
    intro slot; rw [← hR.1 slot]; dsimp only [prepared]; rw [hE]; exact hTable.1 slot
  have hEndpoints : ∀ slot j,RationalHeight (source.threeInput.segmentLottery.P slot j) (expressionHeightBudget s 18) ∧
      RationalHeight (source.threeInput.segmentLottery.Q slot j) (expressionHeightBudget s 18) := by
    intro slot j; rw [← hR.2.1 slot j,← hR.2.2 slot j]; dsimp only [prepared]; rw [hE]; exact hTable.2 slot j
  have hFactory := BinaryGroupFactoryLifetime.mixedTwoPreparedWithTrace_usage input hC ⟨source,hRef⟩ s hs hHeight
  have hDraw := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared.1 source.threeInput.segmentLottery hR
    (expressionHeightBudget s 18) (hs.trans (expressionHeightBudget_ge_input s 18)) hWeight hEndpoints 0 K scalar pc hp
  have hw := wrap_usage 32 2 [prepared.2,(BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.2,(BinaryWordSegmentLifetime.runWithTrace store prepared.1 0 K scalar pc hp).2]) ≤ _
  change usage prepared.2 ≤ _ at hFactory
  unfold mixedEnvelope
  omega

end Blotto.BinaryWordGroupLifetime
