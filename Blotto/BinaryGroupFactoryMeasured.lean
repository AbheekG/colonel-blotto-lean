import Blotto.BinaryThreeFactoryMeasured
import Blotto.BinaryGroupFactoryLifetime

/-! Cached uniform-two/uniform-three and mixed-two inputs produce their actual
measured descriptors and retained sampler records. All orderings and regular/
exceptional regimes are included. Work is compilation/arithmetic/source packing
and control; categorical/point execution and native model joins remain separate. -/

namespace Blotto.BinaryGroupFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option autoImplicit false
set_option maxHeartbeats 3500000

set_option cleanup.letToHave false in
def uniformFactoryWithExtras {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) : ((BinaryStoredOverlapEnvironment.Segment m 9 × Trace) × ℕ) × ℕ :=
by
  by_cases hTwo : m = 2
  · subst m
    let made := BinaryThreeReferenceMeasured.uniformPair input
    exact (((made.1.1,wrap 64 4 [made.1.2]),made.2+8),0)
  · have hThree : m = 3 := hm.resolve_left hTwo
    subst m
    let made := BinaryThreeFactoryMeasured.descriptorWithExtras (uniformThree input)
    exact (((made.1.1.1,wrap 64 4 [made.1.1.2]),made.1.2+8),made.2)

def uniformFactory {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    (BinaryStoredOverlapEnvironment.Segment m 9 × Trace) × ℕ :=
  (uniformFactoryWithExtras input hm).1

theorem uniformFactoryWithExtras_compat {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    (uniformFactoryWithExtras input hm).1 = uniformFactory input hm := rfl

theorem uniformFactory_record {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    uniformFactory input hm = by
  by_cases hTwo : m = 2
  · subst m
    let made := BinaryThreeReferenceMeasured.uniformPair input
    exact ((made.1.1,wrap 64 4 [made.1.2]),made.2+8)
  · have hThree : m = 3 := hm.resolve_left hTwo
    subst m
    let made := BinaryThreeFactoryMeasured.descriptor (uniformThree input)
    exact ((made.1.1,wrap 64 4 [made.1.2]),made.2+8) := by
  rcases hm with rfl | rfl
  · simp only [uniformFactory,uniformFactoryWithExtras,show (2 : ℕ) = 2 from rfl,dif_pos]
  · simp only [uniformFactory,uniformFactoryWithExtras,dif_neg (by decide : ¬(3 : ℕ) = 2),BinaryThreeFactoryMeasured.descriptorWithExtras_compat]

theorem uniformFactory_data {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    (uniformFactory input hm).1.1 = (BinaryGroupFactoryLifetime.uniformFactory input hm).1 := by
  rcases hm with rfl | rfl
  · exact BinaryThreeReferenceMeasured.uniformPair_data input
  · exact BinaryThreeFactoryMeasured.descriptor_data (uniformThree input)

def workEnvelope (s : ℕ) : ℕ := BinaryThreeFactoryMeasured.workEnvelope s+50064
def envelope (s : ℕ) : ℕ := BinaryThreeFactoryMeasured.envelope s+50128

theorem uniformFactory_bounds {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hm : m = 2 ∨ m = 3)
    (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s) :
    (uniformFactory input hm).2 ≤ workEnvelope s ∧ usage (uniformFactory input hm).1.2 ≤ envelope s := by
  rcases hm with rfl | rfl
  · have hW := BinaryThreeReferenceMeasured.uniformPair_work input
    have hU := BinaryThreeReferenceMeasured.uniformPair_usage input
    have hw := wrap_usage 64 4 [(BinaryThreeReferenceMeasured.uniformPair input).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    rw [uniformFactory_record]
    change _+8 ≤ _ ∧ usage (wrap 64 4 [(BinaryThreeReferenceMeasured.uniformPair input).1.2]) ≤ _
    unfold workEnvelope envelope
    exact ⟨by omega,by omega⟩
  · have h := BinaryThreeFactoryMeasured.descriptor_bounds (uniformThree input) (uniformThree_canonical input hC) s hs
      (uniformThree_heights input s hH (by omega))
    have hw := wrap_usage 64 4 [(BinaryThreeFactoryMeasured.descriptor (uniformThree input)).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    rw [uniformFactory_record]
    change _+8 ≤ _ ∧ usage (wrap 64 4 [(BinaryThreeFactoryMeasured.descriptor (uniformThree input)).1.2]) ≤ _
    unfold workEnvelope envelope
    exact ⟨by omega,by omega⟩

set_option cleanup.letToHave false in
def uniformPreparedWithExtras {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) : ((BinaryStoredSegmentProgram.Prepared m 9 × Trace) × ℕ) × ℕ :=
  let produced := uniformFactoryWithExtras input hm
  let made := produced.1
  have hData : made.1.1 = uniformLottery input hm := by
    simpa only [made,produced,uniformFactoryWithExtras_compat] using
      (uniformFactory_data input hm).trans (BinaryGroupFactoryLifetime.uniformFactory_erasure input hC hm)
  (((⟨made.1.1,(by rw [hData]; exact uniformLottery_canonical input hC hm),
    (by rw [hData]; exact (BinaryGroupSamplers.uniformPrepared input hC hAd hm).nonnegative)⟩,
    wrap 16 2 [made.1.2]),made.2+4),produced.2)

def uniformPrepared {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) : (BinaryStoredSegmentProgram.Prepared m 9 × Trace) × ℕ :=
  (uniformPreparedWithExtras input hC hAd hm).1

theorem uniformPreparedWithExtras_compat {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) :
    (uniformPreparedWithExtras input hC hAd hm).1 = uniformPrepared input hC hAd hm := rfl

theorem uniformPrepared_record {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) :
    uniformPrepared input hC hAd hm =
  let made := uniformFactory input hm
  have hData : made.1.1 = uniformLottery input hm :=
    (uniformFactory_data input hm).trans (BinaryGroupFactoryLifetime.uniformFactory_erasure input hC hm)
  ((⟨made.1.1,(by rw [hData]; exact uniformLottery_canonical input hC hm),
    (by rw [hData]; exact (BinaryGroupSamplers.uniformPrepared input hC hAd hm).nonnegative)⟩,
    wrap 16 2 [made.1.2]),made.2+4) := by
  simp only [uniformPrepared,uniformPreparedWithExtras,BinaryThreeFactoryMeasured.orderedWithExtras_compat,BinaryThreeFactoryMeasured.descriptorWithExtras_compat,uniformFactoryWithExtras_compat]

theorem uniformPrepared_data {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) :
    (uniformPrepared input hC hAd hm).1.1 =
      (BinaryGroupFactoryLifetime.uniformPreparedWithTrace input hC hAd hm).1 := by
  simp only [uniformPrepared_record]
  unfold BinaryGroupFactoryLifetime.uniformPreparedWithTrace
  simp only [uniformFactory_data]

theorem uniformPrepared_bounds {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s) :
    (uniformPrepared input hC hAd hm).2 ≤ workEnvelope s+4 ∧
      usage (uniformPrepared input hC hAd hm).1.2 ≤ envelope s+20 := by
  have h := uniformFactory_bounds input hC hm s hs hH
  have hw := wrap_usage 16 2 [(uniformFactory input hm).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [uniformPrepared_record]
  change _+4 ≤ _ ∧ usage (wrap 16 2 [(uniformFactory input hm).1.2]) ≤ _
  exact ⟨by omega,by omega⟩

set_option cleanup.letToHave false in
def mixedTwoPreparedWithExtras (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) : ((BinaryStoredSegmentProgram.Prepared 3 9 × Trace) × ℕ) × ℕ :=
  let produced := BinaryThreeFactoryMeasured.descriptorWithExtras (mixedThree input)
  let made := produced.1
  have hData : made.1.1 = BinaryThreeSpecCompiler.descriptor (mixedThree input) := by
    simpa only [made,produced,BinaryThreeFactoryMeasured.descriptorWithExtras_compat] using
      (BinaryThreeFactoryMeasured.descriptor_data _).trans (BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure _ (mixedThree_canonical input hC))
  (((⟨made.1.1,(by rw [hData]; exact BinaryThreeSpecCompiler.descriptor_canonical _ (mixedThree_canonical input hC)),
    (by rw [hData]; exact (BinaryGroupSamplers.mixedTwoPrepared input hC hAd).nonnegative)⟩,
    wrap 64 4 [made.1.2]),made.2+8),produced.2)

def mixedTwoPrepared (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    (BinaryStoredSegmentProgram.Prepared 3 9 × Trace) × ℕ :=
  (mixedTwoPreparedWithExtras input hC hAd).1

theorem mixedTwoPreparedWithExtras_compat (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    (mixedTwoPreparedWithExtras input hC hAd).1 = mixedTwoPrepared input hC hAd := rfl

theorem mixedTwoPrepared_record (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    mixedTwoPrepared input hC hAd =
  let made := BinaryThreeFactoryMeasured.descriptor (mixedThree input)
  have hData : made.1.1 = BinaryThreeSpecCompiler.descriptor (mixedThree input) :=
    (BinaryThreeFactoryMeasured.descriptor_data _).trans
      (BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure _ (mixedThree_canonical input hC))
  ((⟨made.1.1,(by rw [hData]; exact BinaryThreeSpecCompiler.descriptor_canonical _ (mixedThree_canonical input hC)),
    (by rw [hData]; exact (BinaryGroupSamplers.mixedTwoPrepared input hC hAd).nonnegative)⟩,
    wrap 64 4 [made.1.2]),made.2+8) := by
  simp only [mixedTwoPrepared,mixedTwoPreparedWithExtras,BinaryThreeFactoryMeasured.orderedWithExtras_compat,BinaryThreeFactoryMeasured.descriptorWithExtras_compat,uniformFactoryWithExtras_compat,uniformPreparedWithExtras_compat]

theorem mixedTwoPrepared_data (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    (mixedTwoPrepared input hC hAd).1.1 = (BinaryGroupFactoryLifetime.mixedTwoPreparedWithTrace input hC hAd).1 := by
  simp only [mixedTwoPrepared_record]
  unfold BinaryGroupFactoryLifetime.mixedTwoPreparedWithTrace
  simp only [BinaryThreeFactoryMeasured.descriptor_data]

theorem mixedTwoPrepared_bounds (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s) :
    (mixedTwoPrepared input hC hAd).2 ≤ workEnvelope s ∧
      usage (mixedTwoPrepared input hC hAd).1.2 ≤ envelope s := by
  have h := BinaryThreeFactoryMeasured.descriptor_bounds (mixedThree input) (mixedThree_canonical input hC) s hs
    (mixedThree_heights input s hH)
  have hw := wrap_usage 64 4 [(BinaryThreeFactoryMeasured.descriptor (mixedThree input)).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [mixedTwoPrepared_record]
  change _+8 ≤ _ ∧ usage (wrap 64 4 [(BinaryThreeFactoryMeasured.descriptor (mixedThree input)).1.2]) ≤ _
  unfold workEnvelope envelope
  exact ⟨by omega,by omega⟩

theorem uniform_all_prefix {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (uniformPrepared input hC hAd hm).1.2 steps ≤ borrowed+(envelope s+20) ∧
      framePeak ((uniformPrepared input hC hAd hm).1.2.take steps) ≤ envelope s+20 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (uniformPrepared_bounds input hC hAd hm s hs hH).2 borrowed steps

theorem mixed_all_prefix (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (mixedTwoPrepared input hC hAd).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((mixedTwoPrepared input hC hAd).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (mixedTwoPrepared_bounds input hC hAd s hs hH).2 borrowed steps

end Blotto.BinaryGroupFactoryMeasured
