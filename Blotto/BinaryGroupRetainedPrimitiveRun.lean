import Blotto.BinaryCachedFourRetainedWork
import Blotto.BinaryUnorderedThreeFactoryWork
import Blotto.BinaryAssemblyArithmeticWork

/-! Native group draws retain one descriptor through selection/interpolation;
mixed-three uses the retained four-variable producer. Cached input heights
derive primitive prices. Control/copies/route/physical costs remain separate. -/

namespace Blotto.BinaryGroupRetainedPrimitiveRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs BinaryGroupSamplers
open BinaryCachedThreeDescriptorWork BinaryFactoryHeight

def uniformFactory {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    BinaryStoredOverlapEnvironment.Segment m 9 × ℕ := by
  by_cases h2 : m = 2
  · subst m; exact (uniformLottery input hm,0)
  · have h3 : m = 3 := hm.resolve_left h2
    subst m; exact BinaryUnorderedThreeFactoryWork.descriptorWithWork (uniformThree input)

theorem uniformFactory_state {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    (uniformFactory input hm).1 = uniformLottery input hm := by
  rcases hm with rfl | rfl
  · rfl
  · exact BinaryUnorderedThreeFactoryWork.descriptorWithWork_state _

def factoryBound (s : ℕ) : ℕ := BinaryUnorderedThreeFactoryWork.bound s

theorem uniformFactory_bound {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hm : m = 2 ∨ m = 3)
    (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s) : (uniformFactory input hm).2 ≤ factoryBound s := by
  rcases hm with rfl | rfl
  · exact Nat.zero_le _
  · exact BinaryUnorderedThreeFactoryWork.descriptorWithWork_bound _ (uniformThree_canonical input hC) s hs
      (uniformThree_heights input s hH (by omega))

theorem pair_height (input : UniformInput 2) (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s) : SegmentHeight (pair input) s := by
  refine ⟨?_,?_⟩
  · intro slot; simpa only [pair,FixedArrayTable.read_ofFn] using one_height s hs
  · intro slot j
    simp only [pair,FixedArrayTable.read_ofFn]
    fin_cases j
    · exact ⟨zero_height s hs,hH.1⟩
    · exact ⟨hH.1,zero_height s hs⟩

theorem uniformLottery_height {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hm : m = 2 ∨ m = 3)
    (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s) : SegmentHeight (uniformLottery input hm) (expressionHeightBudget s 18) := by
  rcases hm with rfl | rfl
  · exact (BinaryAssemblyArithmeticWork.pad_height (pair input) 8 0 s hs (pair_height input s hs hH)).mono (expressionHeightBudget_ge_input s 18)
  · exact BinaryUnorderedThreeFactoryWork.descriptor_height _ (uniformThree_canonical input hC) s hs (uniformThree_heights input s hH (by omega))

def uniformPreparedWithWork {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) :
    BinaryStoredSegmentProgram.Prepared m 9 × ℕ :=
  let factory := uniformFactory input hm
  have hc : factory.1.Canonical := by rw [uniformFactory_state]; exact uniformLottery_canonical input hC hm
  have hn : ∀ slot, 0 ≤ value (factory.1.weight.read slot) := by
    rw [uniformFactory_state]; exact (uniformPrepared input hC hAd hm).nonnegative
  (⟨factory.1,hc,hn⟩,factory.2)

theorem uniformPreparedWithWork_state {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) :
    (uniformPreparedWithWork input hC hAd hm).1 = uniformPrepared input hC hAd hm := by
  unfold uniformPreparedWithWork uniformPrepared
  simp only [uniformFactory_state]

def uniformRun {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable m SignedWord) × ℕ) × ℕ :=
  let prepared := uniformPreparedWithWork input hC hAd hm
  let drawn := BinaryStoredSegmentDrawWork.runIndexedWork prepared.1 0 K N scalar bits pos hp
  (drawn.1,prepared.2 + drawn.2)

theorem uniformRun_state {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (uniformRun input hC hAd hm K N scalar bits pos hp).1 = BinaryGroupPartialRun.uniformRun input hC hAd hm K N scalar bits pos hp := by
  unfold uniformRun BinaryGroupPartialRun.uniformRun
  dsimp only
  rw [BinaryStoredSegmentDrawWork.runIndexedWork_state,uniformPreparedWithWork_state]

def descriptorDrawBound (m s K remaining : ℕ) : ℕ := factoryBound s +
  BinaryStoredSegmentChoiceWork.selectionBound 9 (expressionHeightBudget s 18) remaining +
    BinaryStoredSegmentDrawWork.pointBound m (expressionHeightBudget s 18) K

theorem uniformRun_bound {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3)
    (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (uniformRun input hC hAd hm K N scalar bits pos hp).2 ≤ descriptorDrawBound m s K (N - pos) := by
  obtain ⟨source,hr⟩ := hAd
  let prepared := (uniformPreparedWithWork input hC ⟨source,hr⟩ hm).1
  have he := uniformPreparedWithWork_state input hC ⟨source,hr⟩ hm
  have hR : prepared.table.Refines (source.lottery hm) := by change ((uniformPreparedWithWork input hC ⟨source,hr⟩ hm).1).table.Refines _; rw [he]; exact uniformLottery_refines input source hC hr hm
  have hTable := uniformLottery_height input hC hm s hs hH
  have hw : ∀ slot, RationalHeight ((source.lottery hm).weight slot) (expressionHeightBudget s 18) := by
    intro slot; rw [← hR.1 slot]; dsimp only [prepared]; rw [he]; exact hTable.1 slot
  have ht : ∀ slot j, RationalHeight ((source.lottery hm).P slot j) (expressionHeightBudget s 18) ∧ RationalHeight ((source.lottery hm).Q slot j) (expressionHeightBudget s 18) := by
    intro slot j; rw [← hR.2.1 slot j,← hR.2.2 slot j]; dsimp only [prepared]; rw [he]; exact hTable.2 slot j
  have hd := BinaryStoredSegmentDrawWork.runIndexedWork_bound prepared (source.lottery hm) hR _ _
    ((show 2 ≤ s by omega).trans (expressionHeightBudget_ge_input s 18)) hw ht 0 K N scalar bits pos hp
  have hf := uniformFactory_bound input hC hm s hs hH
  have hj := Nat.add_le_add hf hd
  change (uniformRun input hC ⟨source,hr⟩ hm K N scalar bits pos hp).2 ≤ factoryBound s +
    (BinaryStoredSegmentChoiceWork.selectionBound 9 (expressionHeightBudget s 18) (N - pos) +
      BinaryStoredSegmentDrawWork.pointBound m (expressionHeightBudget s 18) K) at hj
  exact hj.trans_eq (by unfold descriptorDrawBound; omega)

def mixedTwoPreparedWithWork (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) : BinaryStoredSegmentProgram.Prepared 3 9 × ℕ :=
  let factory := BinaryUnorderedThreeFactoryWork.descriptorWithWork (mixedThree input)
  have hc : factory.1.Canonical := by rw [BinaryUnorderedThreeFactoryWork.descriptorWithWork_state]; exact BinaryThreeSpecCompiler.descriptor_canonical _ (mixedThree_canonical input hC)
  have hn : ∀ slot, 0 ≤ value (factory.1.weight.read slot) := by
    rw [BinaryUnorderedThreeFactoryWork.descriptorWithWork_state]; exact (mixedTwoPrepared input hC hAd).nonnegative
  (⟨factory.1,hc,hn⟩,factory.2)

theorem mixedTwoPreparedWithWork_state (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    (mixedTwoPreparedWithWork input hC hAd).1 = mixedTwoPrepared input hC hAd := by
  unfold mixedTwoPreparedWithWork mixedTwoPrepared
  simp only [BinaryUnorderedThreeFactoryWork.descriptorWithWork_state]

def mixedRun {m : ℕ} (input : MixedInput m) (hC : input.Canonical) (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : (Option (FixedArrayTable (m+1) SignedWord) × ℕ) × ℕ := by
  by_cases h2 : m = 2
  · subst m
    let prepared := mixedTwoPreparedWithWork input hC hAd
    let drawn := BinaryStoredSegmentDrawWork.runIndexedWork prepared.1 0 K N scalar bits pos hp
    exact (drawn.1,prepared.2 + drawn.2)
  · have h3 : m = 3 := hm.resolve_left h2
    subst m; exact BinaryCachedFourRetainedWork.runIndexed ⟨input,hC,hAd⟩ K N outer scalar bits pos hp

theorem mixedRun_state {m : ℕ} (input : MixedInput m) (hC : input.Canonical) (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (mixedRun input hC hAd hm K N outer scalar bits pos hp).1 = BinaryGroupPartialRun.mixedRun input hC hAd hm K N outer scalar bits pos hp := by
  rcases hm with rfl | rfl
  · change (BinaryStoredSegmentDrawWork.runIndexedWork _ 0 K N scalar bits pos hp).1 = _
    rw [BinaryStoredSegmentDrawWork.runIndexedWork_state,mixedTwoPreparedWithWork_state]
    rfl
  · exact BinaryCachedFourRetainedWork.runIndexed_state _ K N outer scalar bits pos hp

def mixedBound (s K remaining : ℕ) : ℕ := descriptorDrawBound 3 s K remaining + BinaryFourSpecRetainedWork.runBound s K remaining

theorem mixedRun_bound {m : ℕ} (input : MixedInput m) (hC : input.Canonical) (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3)
    (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (mixedRun input hC hAd hm K N outer scalar bits pos hp).2 ≤ mixedBound s K (N - pos) := by
  rcases hm with rfl | rfl
  · obtain ⟨source,hr⟩ := hAd
    let prepared := (mixedTwoPreparedWithWork input hC ⟨source,hr⟩).1
    have he := mixedTwoPreparedWithWork_state input hC ⟨source,hr⟩
    have hR : prepared.table.Refines source.threeInput.segmentLottery := by
      change ((mixedTwoPreparedWithWork input hC ⟨source,hr⟩).1).table.Refines _
      rw [he]; exact BinaryThreeSpecCompiler.descriptor_refines _ _ (mixedThree_canonical input hC) (mixedThree_refines input source hr)
    have hTable := BinaryUnorderedThreeFactoryWork.descriptor_height _ (mixedThree_canonical input hC) s hs (mixedThree_heights input s hH)
    have hw : ∀ slot, RationalHeight (source.threeInput.segmentLottery.weight slot) (expressionHeightBudget s 18) := by
      intro slot; rw [← hR.1 slot]; dsimp only [prepared]; rw [he]; exact hTable.1 slot
    have ht : ∀ slot j, RationalHeight (source.threeInput.segmentLottery.P slot j) (expressionHeightBudget s 18) ∧ RationalHeight (source.threeInput.segmentLottery.Q slot j) (expressionHeightBudget s 18) := by
      intro slot j; rw [← hR.2.1 slot j,← hR.2.2 slot j]; dsimp only [prepared]; rw [he]; exact hTable.2 slot j
    have hd := BinaryStoredSegmentDrawWork.runIndexedWork_bound prepared source.threeInput.segmentLottery hR _ _
      ((show 2 ≤ s by omega).trans (expressionHeightBudget_ge_input s 18)) hw ht 0 K N scalar bits pos hp
    have hf := BinaryUnorderedThreeFactoryWork.descriptorWithWork_bound _ (mixedThree_canonical input hC) s hs (mixedThree_heights input s hH)
    have hj := Nat.add_le_add hf hd
    change (mixedTwoPreparedWithWork input hC ⟨source,hr⟩).2 +
      (BinaryStoredSegmentDrawWork.runIndexedWork prepared 0 K N scalar bits pos hp).2 ≤ factoryBound s +
        (BinaryStoredSegmentChoiceWork.selectionBound 9 (expressionHeightBudget s 18) (N - pos) +
          BinaryStoredSegmentDrawWork.pointBound 3 (expressionHeightBudget s 18) K) at hj
    have hj' := hj.trans_eq (show factoryBound s +
      (BinaryStoredSegmentChoiceWork.selectionBound 9 (expressionHeightBudget s 18) (N - pos) +
        BinaryStoredSegmentDrawWork.pointBound 3 (expressionHeightBudget s 18) K) = descriptorDrawBound 3 s K (N - pos) by
      unfold descriptorDrawBound; omega)
    change (mixedTwoPreparedWithWork input hC ⟨source,hr⟩).2 +
      (BinaryStoredSegmentDrawWork.runIndexedWork prepared 0 K N scalar bits pos hp).2 ≤ _
    exact hj'.trans (Nat.le_add_right (descriptorDrawBound 3 s K (N - pos)) (BinaryFourSpecRetainedWork.runBound s K (N - pos)))
  · exact (BinaryCachedFourRetainedWork.runIndexed_bound ⟨input,hC,hAd⟩ s (by omega) hH K N outer scalar bits pos hp).trans (Nat.le_add_left _ _)

end Blotto.BinaryGroupRetainedPrimitiveRun
