import Blotto.BinaryWordSegmentMeasured
import Blotto.BinaryGroupFactoryMeasured
import Blotto.BinaryWordGroupLifetime
import Blotto.BinaryWordSegmentLifetimeBound
import Blotto.BinaryGroupReachedHeight
import Blotto.BinaryPRGWordControllerTerminal

/-! Measured descriptor factories feed complete measured categorical/physical
point draws. The work field now joins factory and selected draw source work.
Exact old rows/cursors and enlarged factory retained-source bounds are preserved.
Route emission and complete terminal adoption, four-variable factories and native
model prices remain separate obligations. -/
namespace Blotto.BinaryWordGroupDrawMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 2000000

set_option cleanup.letToHave false in
def uniformRunWithFactoryExtras {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerTerminal.Result store m × Trace) × ℕ) × ℕ) × ℕ :=
  let all := BinaryGroupFactoryMeasured.uniformPreparedWithExtras input hC hAd hm
  let prepared := all.1
  let produced := BinaryWordSegmentMeasured.runWithExtras store prepared.1.1 0 K scalar pc hp
  let drawn := produced.1
  ((((drawn.1.1,wrap 32 2 [prepared.1.2,drawn.1.2]),prepared.2+drawn.2+8),produced.2),all.2)

def uniformRunWithDrawExtras {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerTerminal.Result store m × Trace) × ℕ) × ℕ :=
  (uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).1

theorem uniformRunWithFactoryExtras_compat {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).1 = uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp := rfl

theorem uniformRunWithDrawExtras_record {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp =
  let prepared := BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm
  let produced := BinaryWordSegmentMeasured.runWithExtras store prepared.1.1 0 K scalar pc hp
  let drawn := produced.1
  (((drawn.1.1,wrap 32 2 [prepared.1.2,drawn.1.2]),prepared.2+drawn.2+8),produced.2) := by
  simp only [uniformRunWithDrawExtras,uniformRunWithFactoryExtras,BinaryGroupFactoryMeasured.uniformFactoryWithExtras_compat,BinaryGroupFactoryMeasured.uniformPreparedWithExtras_compat,BinaryGroupFactoryMeasured.mixedTwoPreparedWithExtras_compat]

def uniformRun {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (BinaryPRGWordControllerTerminal.Result store m × Trace) × ℕ :=
  (uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp).1

theorem uniformRunWithDrawExtras_compat {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (uniformRunWithDrawExtras store input hC hAd hm K scalar pc hp).1 = uniformRun store input hC hAd hm K scalar pc hp := rfl

theorem uniformRun_record {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : uniformRun store input hC hAd hm K scalar pc hp =
  let prepared := BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm
  let drawn := BinaryWordSegmentMeasured.run store prepared.1.1 0 K scalar pc hp
  ((drawn.1.1,wrap 32 2 [prepared.1.2,drawn.1.2]),prepared.2+drawn.2+8) := by
  rfl

theorem uniformRun_data {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm K scalar pc hp).1.1 =
      (BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp).1 := by
  simp only [uniformRun_record,BinaryWordGroupLifetime.uniformRun,BinaryGroupFactoryMeasured.uniformPrepared_data,BinaryWordSegmentMeasured.run_erases]

set_option cleanup.letToHave false in
def mixedTwoRunWithFactoryExtras (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((BinaryPRGWordControllerTerminal.Result store 3 × Trace) × ℕ) × ℕ) × ℕ :=
  let all := BinaryGroupFactoryMeasured.mixedTwoPreparedWithExtras input hC hAd
  let prepared := all.1
  let produced := BinaryWordSegmentMeasured.runWithExtras store prepared.1.1 0 K scalar pc hp
  let drawn := produced.1
  ((((drawn.1.1,wrap 32 2 [prepared.1.2,drawn.1.2]),prepared.2+drawn.2+8),produced.2),all.2)

def mixedTwoRunWithDrawExtras (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : ((BinaryPRGWordControllerTerminal.Result store 3 × Trace) × ℕ) × ℕ :=
  (mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).1

theorem mixedTwoRunWithFactoryExtras_compat (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).1 = mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp := rfl

theorem mixedTwoRunWithDrawExtras_record (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp =
  let prepared := BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd
  let produced := BinaryWordSegmentMeasured.runWithExtras store prepared.1.1 0 K scalar pc hp
  let drawn := produced.1
  (((drawn.1.1,wrap 32 2 [prepared.1.2,drawn.1.2]),prepared.2+drawn.2+8),produced.2) := by
  simp only [mixedTwoRunWithDrawExtras,mixedTwoRunWithFactoryExtras,BinaryGroupFactoryMeasured.uniformFactoryWithExtras_compat,BinaryGroupFactoryMeasured.uniformPreparedWithExtras_compat,BinaryGroupFactoryMeasured.mixedTwoPreparedWithExtras_compat,uniformRunWithFactoryExtras_compat]

def mixedTwoRun (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (BinaryPRGWordControllerTerminal.Result store 3 × Trace) × ℕ :=
  (mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp).1

theorem mixedTwoRunWithDrawExtras_compat (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (mixedTwoRunWithDrawExtras store input hC hAd K scalar pc hp).1 = mixedTwoRun store input hC hAd K scalar pc hp := rfl

theorem mixedTwoRun_record (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : mixedTwoRun store input hC hAd K scalar pc hp =
  let prepared := BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd
  let drawn := BinaryWordSegmentMeasured.run store prepared.1.1 0 K scalar pc hp
  ((drawn.1.1,wrap 32 2 [prepared.1.2,drawn.1.2]),prepared.2+drawn.2+8) := by
  rfl

theorem mixedTwoRun_data (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd K scalar pc hp).1.1 =
      (BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp).1 := by
  simp only [mixedTwoRun_record,BinaryWordGroupLifetime.mixedTwoRun,BinaryGroupFactoryMeasured.mixedTwoPrepared_data,BinaryWordSegmentMeasured.run_erases]

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
  have hDraw := BinaryWordSegmentMeasured.run_usage store prepared.1.1 (source.lottery hm) hR
    (expressionHeightBudget s 18) (hs.trans (expressionHeightBudget_ge_input s 18)) hWeight hEndpoints 0 K scalar pc hp
  have hw := wrap_usage 32 2 [prepared.1.2,(BinaryWordSegmentMeasured.run store prepared.1.1 0 K scalar pc hp).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.1.2,(BinaryWordSegmentMeasured.run store prepared.1.1 0 K scalar pc hp).1.2]) ≤ _
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
  have hDraw := BinaryWordSegmentMeasured.run_usage store prepared.1.1 source.threeInput.segmentLottery hR
    (expressionHeightBudget s 18) (hs.trans (expressionHeightBudget_ge_input s 18)) hWeight hEndpoints 0 K scalar pc hp
  have hw := wrap_usage 32 2 [prepared.1.2,(BinaryWordSegmentMeasured.run store prepared.1.1 0 K scalar pc hp).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [prepared.1.2,(BinaryWordSegmentMeasured.run store prepared.1.1 0 K scalar pc hp).1.2]) ≤ _
  change usage prepared.1.2 ≤ _ at hFactory
  unfold mixedEnvelope
  omega

def uniformPrice (m s K i cap : ℕ) : ℕ := BinaryGroupFactoryMeasured.workEnvelope s+
  BinaryWordSegmentMeasured.workEnvelope m 9 (expressionHeightBudget s 18) K i cap+12

def mixedPrice (s K i cap : ℕ) : ℕ := BinaryGroupFactoryMeasured.workEnvelope s+
  BinaryWordSegmentMeasured.workEnvelope 3 9 (expressionHeightBudget s 18) K i cap+8

theorem uniformRun_work {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm K scalar pc hp).2 ≤ uniformPrice m s K store.width store.cap.value := by
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
  have hFactory := (BinaryGroupFactoryMeasured.uniformPrepared_bounds input hC ⟨source,hRef⟩ hm s hs hHeight).1
  have hDraw := BinaryWordSegmentMeasured.run_work store prepared.1.1 (source.lottery hm) hR
    (expressionHeightBudget s 18) hWeight hEndpoints 0 K scalar pc hp
  change prepared.2+(BinaryWordSegmentMeasured.run store prepared.1.1 0 K scalar pc hp).2+8 ≤ _
  unfold uniformPrice
  change prepared.2 ≤ _ at hFactory
  omega

theorem mixedTwoRun_work (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd K scalar pc hp).2 ≤ mixedPrice s K store.width store.cap.value := by
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
  have hFactory := (BinaryGroupFactoryMeasured.mixedTwoPrepared_bounds input hC ⟨source,hRef⟩ s hs hHeight).1
  have hDraw := BinaryWordSegmentMeasured.run_work store prepared.1.1 source.threeInput.segmentLottery hR
    (expressionHeightBudget s 18) hWeight hEndpoints 0 K scalar pc hp
  change prepared.2+(BinaryWordSegmentMeasured.run store prepared.1.1 0 K scalar pc hp).2+8 ≤ _
  unfold mixedPrice
  change prepared.2 ≤ _ at hFactory
  omega

theorem uniformRun_position {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (uniformRun store input hC hAd hm K scalar pc hp).1.1.2.value ∧
      (uniformRun store input hC hAd hm K scalar pc hp).1.1.2.value ≤ store.cap.value :=
  BinaryWordSegmentMeasured.run_position store
    (BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm).1.1 0 K scalar pc hp

theorem mixedTwoRun_position (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (mixedTwoRun store input hC hAd K scalar pc hp).1.1.2.value ∧
      (mixedTwoRun store input hC hAd K scalar pc hp).1.1.2.value ≤ store.cap.value :=
  BinaryWordSegmentMeasured.run_position store
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

end Blotto.BinaryWordGroupDrawMeasured
