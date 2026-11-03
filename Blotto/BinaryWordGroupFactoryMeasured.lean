import Blotto.BinaryScalarTape
import Blotto.BinaryGroupFactoryMeasured
import Blotto.BinaryWordGroupLifetime
import Blotto.BinaryWordSegmentLifetimeBound
import Blotto.BinaryGroupReachedHeight
import Blotto.BinaryPRGWordControllerTerminal

/-! Actual uniform and mixed-two draws consume the returned measured factory
record once. The work field covers factory and wrapper source work; categorical
selection/point execution and native model prices remain separate. Exact old
row/cursor data and all original-height retained-source contracts are preserved. -/
namespace Blotto.BinaryWordGroupFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

def uniformRun {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (BinaryPRGWordControllerTerminal.Result store m × Trace) × ℕ :=
  let prepared := BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared.1.1 0 K scalar pc hp
  ((drawn.1,wrap 32 2 [prepared.1.2,drawn.2]),prepared.2+8)

theorem uniformRun_data {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm K scalar pc hp).1.1 =
      (BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp).1 := by
  simp only [uniformRun,BinaryWordGroupLifetime.uniformRun,BinaryGroupFactoryMeasured.uniformPrepared_data]

def mixedTwoRun (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (BinaryPRGWordControllerTerminal.Result store 3 × Trace) × ℕ :=
  let prepared := BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared.1.1 0 K scalar pc hp
  ((drawn.1,wrap 32 2 [prepared.1.2,drawn.2]),prepared.2+8)

theorem mixedTwoRun_data (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd K scalar pc hp).1.1 =
      (BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp).1 := by
  simp only [mixedTwoRun,BinaryWordGroupLifetime.mixedTwoRun,BinaryGroupFactoryMeasured.mixedTwoPrepared_data]

def uniformEnvelope (m s K indexWidth seedCap : ℕ) : ℕ := BinaryGroupFactoryMeasured.envelope s + 20 +
  BinaryWordSegmentLifetimeBound.envelope m 9 (expressionHeightBudget s 18) K indexWidth seedCap + 64

def mixedEnvelope (s K indexWidth seedCap : ℕ) : ℕ := BinaryGroupFactoryMeasured.envelope s +
  BinaryWordSegmentLifetimeBound.envelope 3 9 (expressionHeightBudget s 18) K indexWidth seedCap + 64

theorem uniformRun_usage {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (uniformRun store input hC hAd hm K scalar pc hp).1.2 ≤ uniformEnvelope m s K store.width store.cap.value := by
  obtain ⟨source,hRef⟩ := hAd
  let prepared := BinaryGroupFactoryMeasured.uniformPrepared input hC ⟨source,hRef⟩ hm
  have hE := (BinaryGroupFactoryMeasured.uniformPrepared_data input hC ⟨source,hRef⟩ hm).trans
    (BinaryGroupFactoryLifetime.uniformPreparedWithTrace_erasure input hC ⟨source,hRef⟩ hm)
  have hR : prepared.1.1.table.Refines (source.lottery hm) := by
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
  have hFactory := (BinaryGroupFactoryMeasured.uniformPrepared_bounds input hC ⟨source,hRef⟩ hm s hs hHeight).2
  have hDraw := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared.1.1 (source.lottery hm) hR
    (expressionHeightBudget s 18) (hs.trans (expressionHeightBudget_ge_input s 18)) hWeight hEndpoints 0 K scalar pc hp
  have hw := wrap_usage 32 2 [prepared.1.2,(BinaryWordSegmentLifetime.runWithTrace store prepared.1.1 0 K scalar pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.1.2,(BinaryWordSegmentLifetime.runWithTrace store prepared.1.1 0 K scalar pc hp).2]) ≤ _
  change usage prepared.1.2 ≤ _ at hFactory
  unfold uniformEnvelope
  omega

theorem mixedTwoRun_usage (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (mixedTwoRun store input hC hAd K scalar pc hp).1.2 ≤ mixedEnvelope s K store.width store.cap.value := by
  obtain ⟨source,hRef⟩ := hAd
  let prepared := BinaryGroupFactoryMeasured.mixedTwoPrepared input hC ⟨source,hRef⟩
  have hE := (BinaryGroupFactoryMeasured.mixedTwoPrepared_data input hC ⟨source,hRef⟩).trans
    (BinaryGroupFactoryLifetime.mixedTwoPreparedWithTrace_erasure input hC ⟨source,hRef⟩)
  have hR : prepared.1.1.table.Refines source.threeInput.segmentLottery := by
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
  have hFactory := (BinaryGroupFactoryMeasured.mixedTwoPrepared_bounds input hC ⟨source,hRef⟩ s hs hHeight).2
  have hDraw := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared.1.1 source.threeInput.segmentLottery hR
    (expressionHeightBudget s 18) (hs.trans (expressionHeightBudget_ge_input s 18)) hWeight hEndpoints 0 K scalar pc hp
  have hw := wrap_usage 32 2 [prepared.1.2,(BinaryWordSegmentLifetime.runWithTrace store prepared.1.1 0 K scalar pc hp).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.1.2,(BinaryWordSegmentLifetime.runWithTrace store prepared.1.1 0 K scalar pc hp).2]) ≤ _
  change usage prepared.1.2 ≤ _ at hFactory
  unfold mixedEnvelope
  omega

theorem uniformRun_work {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm K scalar pc hp).2 ≤ BinaryGroupFactoryMeasured.workEnvelope s+12 := by
  have h := (BinaryGroupFactoryMeasured.uniformPrepared_bounds input hC hAd hm s hs hH).1
  change _+8 ≤ _
  omega

theorem mixedTwoRun_work (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd K scalar pc hp).2 ≤ BinaryGroupFactoryMeasured.workEnvelope s+8 := by
  have h := (BinaryGroupFactoryMeasured.mixedTwoPrepared_bounds input hC hAd s hs hH).1
  change _+8 ≤ _
  omega

theorem uniformRun_position {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (uniformRun store input hC hAd hm K scalar pc hp).1.1.2.value ∧
      (uniformRun store input hC hAd hm K scalar pc hp).1.1.2.value ≤ store.cap.value :=
  BinaryWordSegmentLifetime.runWithTrace_position store
    (BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm).1.1 0 K scalar pc hp

theorem mixedTwoRun_position (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (mixedTwoRun store input hC hAd K scalar pc hp).1.1.2.value ∧
      (mixedTwoRun store input hC hAd K scalar pc hp).1.1.2.value ≤ store.cap.value :=
  BinaryWordSegmentLifetime.runWithTrace_position store
    (BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd).1.1 0 K scalar pc hp

theorem uniform_all_prefix {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (uniformRun store input hC hAd hm K scalar pc hp).1.2 steps ≤
      borrowed+uniformEnvelope m s K store.width store.cap.value ∧
    framePeak ((uniformRun store input hC hAd hm K scalar pc hp).1.2.take steps) ≤
      uniformEnvelope m s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (uniformRun_usage store input hC hAd hm s hs hH K scalar pc hp) borrowed steps

theorem mixed_all_prefix (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (mixedTwoRun store input hC hAd K scalar pc hp).1.2 steps ≤
      borrowed+mixedEnvelope s K store.width store.cap.value ∧
    framePeak ((mixedTwoRun store input hC hAd K scalar pc hp).1.2.take steps) ≤
      mixedEnvelope s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (mixedTwoRun_usage store input hC hAd s hs hH K scalar pc hp) borrowed steps

end Blotto.BinaryWordGroupFactoryMeasured
