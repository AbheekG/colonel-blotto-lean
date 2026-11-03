import Blotto.BinaryPRGWordControllerFourWork
import Blotto.BinaryGroupRetainedPrimitiveRun

/-! Concrete Store group draws join the source three-variable factory or
complete four continuation with the actually selected Boolean arithmetic
backend.  Uniform-two, uniform-three, mixed-two and mixed-three keep their
original prepared inputs.  This is a source primitive/control/cell component
composition; physical table-address/compiler interpretation is separate. -/

namespace Blotto.BinaryPRGWordControllerGroupWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork

def uniformRun {m : ℕ} (store : Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store m × ℕ :=
  let factory := BinaryGroupRetainedPrimitiveRun.uniformPreparedWithWork input hC hAd hm
  let drawn := BinaryPRGWordControllerWork.segmentWithWork store factory.1 0 K scalar pc hp
  (drawn.1, factory.2 + drawn.2 + 20)

theorem uniformRun_erasure {m : ℕ} (store : Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm K scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.uniformRun store input hC hAd hm K scalar pc hp := by
  unfold uniformRun BinaryPRGWordControllerTerminal.uniformRun
  dsimp only
  rw [BinaryPRGWordControllerWork.segmentWithWork_erasure,
    BinaryGroupRetainedPrimitiveRun.uniformPreparedWithWork_state]

def uniformBound (m s K indexWidth remaining : ℕ) : ℕ := BinaryGroupRetainedPrimitiveRun.factoryBound s +
  BinaryPRGWordControllerWork.segmentBound m 9 (expressionHeightBudget s 18) K indexWidth remaining + 20

theorem uniformRun_bound {m : ℕ} (store : Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s)
    (hH : UniformHeights input s) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRun store input hC hAd hm K scalar pc hp).2 ≤ uniformBound m s K store.width (store.cap.value - pc.value) := by
  obtain ⟨source, hr⟩ := hAd
  let prepared := (BinaryGroupRetainedPrimitiveRun.uniformPreparedWithWork input hC ⟨source, hr⟩ hm).1
  have he := BinaryGroupRetainedPrimitiveRun.uniformPreparedWithWork_state input hC ⟨source, hr⟩ hm
  have hR : prepared.table.Refines (source.lottery hm) := by
    dsimp only [prepared]
    rw [he]
    exact uniformLottery_refines input source hC hr hm
  have hTable := BinaryGroupRetainedPrimitiveRun.uniformLottery_height input hC hm s hs hH
  have hWeight : ∀ slot, RationalHeight ((source.lottery hm).weight slot) (expressionHeightBudget s 18) := by
    intro slot
    rw [← hR.1 slot]
    dsimp only [prepared]
    rw [he]
    exact hTable.1 slot
  have hPoint : ∀ slot j, RationalHeight (value ((prepared.table.P.read slot).read j)) (expressionHeightBudget s 18) ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) (expressionHeightBudget s 18) := by
    intro slot j
    dsimp only [prepared]
    rw [he]
    exact hTable.2 slot j
  have hDraw := BinaryPRGWordControllerWork.segmentWithWork_bound store prepared (source.lottery hm) hR
    (expressionHeightBudget s 18) ((by omega : 2 ≤ s).trans (expressionHeightBudget_ge_input s 18))
    hWeight hPoint 0 K scalar pc hp
  have hFactory := BinaryGroupRetainedPrimitiveRun.uniformFactory_bound input hC hm s hs hH
  unfold uniformRun uniformBound
  dsimp only
  change (BinaryGroupRetainedPrimitiveRun.uniformFactory input hm).2 +
    (BinaryPRGWordControllerWork.segmentWithWork store prepared 0 K scalar pc hp).2 + 20 ≤ _
  omega

def mixedTwoRun (store : Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store 3 × ℕ :=
  let factory := BinaryGroupRetainedPrimitiveRun.mixedTwoPreparedWithWork input hC hAd
  let drawn := BinaryPRGWordControllerWork.segmentWithWork store factory.1 0 K scalar pc hp
  (drawn.1, factory.2 + drawn.2 + 20)

theorem mixedTwoRun_erasure (store : Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd K scalar pc hp).1 =
      BinaryPRGWordControllerSegment.run store (mixedTwoPrepared input hC hAd) 0 K scalar pc hp := by
  unfold mixedTwoRun
  dsimp only
  rw [BinaryPRGWordControllerWork.segmentWithWork_erasure,
    BinaryGroupRetainedPrimitiveRun.mixedTwoPreparedWithWork_state]

theorem mixedTwoRun_bound (store : Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s)
    (K : ℕ) (scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRun store input hC hAd K scalar pc hp).2 ≤ uniformBound 3 s K store.width (store.cap.value - pc.value) := by
  obtain ⟨source, hr⟩ := hAd
  let prepared := (BinaryGroupRetainedPrimitiveRun.mixedTwoPreparedWithWork input hC ⟨source, hr⟩).1
  have he := BinaryGroupRetainedPrimitiveRun.mixedTwoPreparedWithWork_state input hC ⟨source, hr⟩
  have hR : prepared.table.Refines source.threeInput.segmentLottery := by
    dsimp only [prepared]
    rw [he]
    exact BinaryThreeSpecCompiler.descriptor_refines _ _ (mixedThree_canonical input hC) (mixedThree_refines input source hr)
  have hTable := BinaryUnorderedThreeFactoryWork.descriptor_height _ (mixedThree_canonical input hC) s hs
    (mixedThree_heights input s hH)
  have hWeight : ∀ slot, RationalHeight (source.threeInput.segmentLottery.weight slot) (expressionHeightBudget s 18) := by
    intro slot
    rw [← hR.1 slot]
    dsimp only [prepared]
    rw [he]
    exact hTable.1 slot
  have hPoint : ∀ slot j, RationalHeight (value ((prepared.table.P.read slot).read j)) (expressionHeightBudget s 18) ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) (expressionHeightBudget s 18) := by
    intro slot j
    dsimp only [prepared]
    rw [he]
    exact hTable.2 slot j
  have hDraw := BinaryPRGWordControllerWork.segmentWithWork_bound store prepared source.threeInput.segmentLottery hR
    (expressionHeightBudget s 18) ((by omega : 2 ≤ s).trans (expressionHeightBudget_ge_input s 18))
    hWeight hPoint 0 K scalar pc hp
  have hFactory := BinaryUnorderedThreeFactoryWork.descriptorWithWork_bound _ (mixedThree_canonical input hC) s hs
    (mixedThree_heights input s hH)
  unfold mixedTwoRun uniformBound BinaryGroupRetainedPrimitiveRun.factoryBound
  dsimp only
  change (BinaryUnorderedThreeFactoryWork.descriptorWithWork (mixedThree input)).2 +
    (BinaryPRGWordControllerWork.segmentWithWork store prepared 0 K scalar pc hp).2 + 20 ≤ _
  omega

def mixedRun {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store (m + 1) × ℕ := by
  by_cases h2 : m = 2
  · subst m
    exact mixedTwoRun store input hC hAd K scalar pc hp
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact BinaryPRGWordControllerFourWork.restoredRun store (mixedFour input) (mixedFour_canonical input hC)
      (mixedFour_admissible input hC hAd) K outer scalar pc hp

theorem mixedRun_erasure {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedRun store input hC hAd hm K outer scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.mixedRun store input hC hAd hm K outer scalar pc hp := by
  rcases hm with rfl | rfl
  · exact mixedTwoRun_erasure _ _ _ _ _ _ _ _
  · exact BinaryPRGWordControllerFourWork.restoredRun_erasure _ _ _ _ _ _ _ _ _

def mixedBound (s K indexWidth remaining : ℕ) : ℕ := uniformBound 3 s K indexWidth remaining +
  BinaryPRGWordControllerFourWork.restoredBound s K indexWidth remaining

theorem mixedRun_bound {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s)
    (hH : MixedHeights input s) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedRun store input hC hAd hm K outer scalar pc hp).2 ≤ mixedBound s K store.width (store.cap.value - pc.value) := by
  rcases hm with rfl | rfl
  · exact (mixedTwoRun_bound store input hC hAd s hs hH K scalar pc hp).trans (Nat.le_add_right _ _)
  · obtain ⟨source, hr⟩ := hAd
    exact (BinaryPRGWordControllerFourWork.restoredRun_bound store (mixedFour input) source.fourInput
      (mixedFour_canonical input hC) (mixedFour_refines input source hr) (mixedFour_admissible input hC ⟨source, hr⟩)
      s (by omega) (BinaryCachedFourParameterWork.source_four_heights input source hr s hH)
      K outer scalar pc hp).trans (Nat.le_add_left _ _)

end Blotto.BinaryPRGWordControllerGroupWork
