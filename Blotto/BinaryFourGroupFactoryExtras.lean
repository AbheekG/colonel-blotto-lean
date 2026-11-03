import Blotto.BinaryReturnedDrawFactoryExtras
import Blotto.BinaryReturnedControlExtras

/-! Factory, draw and reached control costs use disjoint actual source work.
All preceding records and all old price premises remain exact. -/
namespace Blotto.BinaryFourGroupFactoryExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local irreducible] BinaryFourSmallMeasured.afterRootWithFactoryExtras BinaryFourSmallMeasured.runWithFactoryExtras BinaryFourOrderedMeasured.runWithFactoryExtras BinaryFourRestoredMeasured.afterOrderWithFactoryExtras BinaryFourRestoredMeasured.runWithFactoryExtras BinaryWordGroupDrawMeasured.uniformRunWithFactoryExtras BinaryWordGroupDrawMeasured.mixedTwoRunWithFactoryExtras BinaryFourGluingDrawMeasured.runWithFactoryExtras BinaryFourSmallUniformDrawMeasured.runWithFactoryExtras BinaryReflectedDrawMeasured.runWithFactoryExtras BinaryFourSmallCoinMeasured.sampleWithExtras BinaryFourGuardMeasured.guardWithExtras BinaryWordSegmentMeasured.runWithExtras BinaryGroupFactoryMeasured.uniformPreparedWithExtras BinaryGroupFactoryMeasured.mixedTwoPreparedWithExtras

namespace Small
open BinaryFourSmallMeasured

theorem after_root_joint (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) (E : ℕ) (hE : E ≤155*root.2) :
    (afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1.2+(afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).2+E ≤155*(afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1.1.2 := by
  simp only [afterRootWithFactoryExtras]
  cases h : root.1.1.1 with
  | none => dsimp only; omega
  | some branch =>
      cases branch
      · have hd := BinaryReturnedDrawFactoryExtras.Reflected.run_combined store input hC hAd K outer scalar root.1.1.2 hNext
        dsimp only
        omega
      · have hd := BinaryReturnedDrawFactoryExtras.SmallUniform.run_combined store input hC hAd K scalar root.1.1.2 hNext
        dsimp only
        omega

theorem after_root_combined (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    (afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1.2+(afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).2 ≤155*(afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1.1.2 := by
  simpa only [Nat.add_zero] using after_root_joint store input hC hAd K outer scalar root hNext 0 (by omega)

theorem run_combined (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2 := by
  have hr := BinaryReturnedControlExtras.root_bound store input pc hp
  have h := after_root_joint store input hC hAd K outer scalar (BinaryFourSmallCoinMeasured.sampleWithExtras store input pc hp).1
    (by simpa only [BinaryFourSmallCoinMeasured.sampleWithExtras_compat] using (BinaryFourSmallCoinMeasured.sample_position store input pc hp).2)
    (BinaryFourSmallCoinMeasured.sampleWithExtras store input pc hp).2 hr
  simp only [runWithFactoryExtras]
  omega

end Small

namespace Ordered
open BinaryFourOrderedMeasured

theorem run_combined (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2 := by
  have hg := BinaryReturnedControlExtras.guard_bound input
  simp only [runWithFactoryExtras]
  split
  · rename_i hSelected
    have hOld : BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hSelected
    have hd := BinaryReturnedDrawFactoryExtras.Gluing.run_combined store input hC
      (BinaryFourGluingDrawLifetime.sampler_admissible input hC hAd hOld) K scalar pc hp
    dsimp only [join]
    omega
  · rename_i hSelected
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := by
      rw [← BinaryFourGuardLifetime.guardWithTrace_erasure input hC,← BinaryFourGuardMeasured.guard_erases]; exact hSelected
    have hd := Small.run_combined store input hC (BinaryFourAdmissibility.small_guard input hC hAd hOld) K outer scalar pc hp
    dsimp only [join]
    omega

end Ordered

namespace Restored
open BinaryFourRestoredMeasured

theorem after_order_combined (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.1.2+(afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.2+(afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).2 ≤155*(afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.1.1.2 := by
  have hOrderedC : ordered.1.1.1.Canonical := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_canonical input hC
  have hOrderedAd : BinaryFourAdmissibility.Admissible ordered.1.1.1 := by rw [hOrdered]; exact BinaryFourSpecSampler.orderedInput_admissible input hC hAd
  have hd := Ordered.run_combined store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp
  have hw := BinaryReturnedTerminalDrawExtras.restore_source_dominates store ordered
    (BinaryFourOrderedMeasured.runWithFactoryExtras store ordered.1.1.1 hOrderedC hOrderedAd K outer scalar pc hp).1.1.1
  simp only [afterOrderWithFactoryExtras]
  omega

theorem run_combined (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2 := by
  simp only [runWithFactoryExtras]
  exact after_order_combined store input hC hAd _ _ K outer scalar pc hp

end Restored

namespace GroupDraw
open BinaryWordGroupDrawMeasured

theorem uniformRun_combined {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).1.2+(uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).2 ≤155*(uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).1.1.2 := by
  have hPrepared := BinaryPreparedFactoryNormalizationExtras.GroupFactory.uniformPrepared_extra input hC hAd hm
  have hd := BinaryReturnedCategoricalExtras.segment_bound store (BinaryGroupFactoryMeasured.uniformPreparedWithExtras input hC hAd hm).1.1.1 0 K scalar pc hp
  simp only [uniformRunWithFactoryExtras]
  omega

theorem mixedTwoRun_combined (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).1.2+(mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤155*(mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2 := by
  have hPrepared := BinaryPreparedFactoryNormalizationExtras.GroupFactory.mixedTwoPrepared_extra input hC hAd
  have hd := BinaryReturnedCategoricalExtras.segment_bound store (BinaryGroupFactoryMeasured.mixedTwoPreparedWithExtras input hC hAd).1.1.1 0 K scalar pc hp
  simp only [mixedTwoRunWithFactoryExtras]
  omega

end GroupDraw

namespace Small
open BinaryFourSmallMeasured

theorem afterRoot_factory (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value) :
    (afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).2 ≤155*(afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1.1.2 := by
  have h := after_root_combined store input hC hAd K outer scalar root hNext
  omega

theorem afterRoot_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (root : Root store) (hNext : root.1.1.2.value ≤ store.cap.value)
    (hRoot : root.2 ≤ BinaryFourSmallCoinMeasured.workEnvelope s store.width store.cap.value ∧
      usage root.1.2 ≤ BinaryFourSmallCoinLifetime.envelope s store.width store.cap.value) :
    (afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1.1.2+(afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1.2+(afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).2 ≤156*(workEnvelope s K store.width store.cap.value) ∧
      usage (afterRootWithFactoryExtras store input hC hAd K outer scalar root hNext).1.1.1.2 ≤ envelope s K store.width store.cap.value := by
  have he := after_root_combined store input hC hAd K outer scalar root hNext
  have ho := afterRoot_bounds store input source hC hR hCase hAd s hs hH K outer scalar root hNext hRoot
  simp only [afterRootWithFactoryExtras_compat,afterRootWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end Small

namespace Small
open BinaryFourSmallMeasured

theorem run_factory (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2 := by
  have h := run_combined store input hC hAd K outer scalar pc hp
  omega

theorem run_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤156*(workEnvelope s K store.width store.cap.value) ∧
      usage (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.1.2 ≤ envelope s K store.width store.cap.value := by
  have he := run_combined store input hC hAd K outer scalar pc hp
  have ho := run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp
  simp only [runWithFactoryExtras_compat,runWithControlExtras_compat,runWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end Small

namespace Ordered
open BinaryFourOrderedMeasured

theorem run_factory (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2 := by
  have h := run_combined store input hC hAd K outer scalar pc hp
  omega

theorem run_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤156*(workEnvelope s K store.width store.cap.value) ∧
      usage (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.1.2 ≤ envelope s K store.width store.cap.value := by
  have he := run_combined store input hC hAd K outer scalar pc hp
  have ho := run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp
  simp only [runWithFactoryExtras_compat,runWithControlExtras_compat,runWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end Ordered

namespace Restored
open BinaryFourRestoredMeasured

theorem afterOrder_factory (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).2 ≤155*(afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.1.1.2 := by
  have h := after_order_combined store input hC hAd ordered hOrdered K outer scalar pc hp
  omega

theorem afterOrder_price (store : BinarySeedLookupTree.Store) (input : Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (ordered : Ordered)
    (hOrdered : ordered.1.1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input))
    (P U : ℕ) (hOrder : ordered.2 ≤ P ∧ usage ordered.1.2 ≤ U)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.1.1.2+(afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.1.2+(afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.2+(afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).2 ≤156*(P+BinaryFourOrderedMeasured.workEnvelope s K store.width store.cap.value+1700) ∧
      usage (afterOrderWithFactoryExtras store input hC hAd ordered hOrdered K outer scalar pc hp).1.1.1.1.2 ≤ U+BinaryFourOrderedMeasured.envelope s K store.width store.cap.value+1100 := by
  have he := after_order_combined store input hC hAd ordered hOrdered K outer scalar pc hp
  have ho := afterOrder_bounds store input source hC hR hAd s hs hH ordered hOrdered P U hOrder K outer scalar pc hp
  simp only [afterOrderWithFactoryExtras_compat,afterOrderWithControlExtras_compat,afterOrderWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end Restored

namespace Restored
open BinaryFourRestoredMeasured

theorem run_factory (store : BinarySeedLookupTree.Store) (input : Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2 := by
  have h := run_combined store input hC hAd K outer scalar pc hp
  omega

theorem run_price (store : BinarySeedLookupTree.Store) (input : Input) (source : RationalFourSpec)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourSpecSampler.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤156*(workEnvelope s K store.width store.cap.value) ∧
      usage (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.1.2 ≤ envelope s K store.width store.cap.value := by
  have he := run_combined store input hC hAd K outer scalar pc hp
  have ho := run_bounds store input source hC hR hAd s hs hH K outer scalar pc hp
  simp only [runWithFactoryExtras_compat,runWithControlExtras_compat,runWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end Restored

namespace GroupDraw
open BinaryWordGroupDrawMeasured

theorem uniformRun_factory {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).2 ≤155*(uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).1.1.2 := by
  have h := uniformRun_combined store input hC hAd hm K scalar pc hp
  omega

theorem uniformRun_price {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hHeight : UniformHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).1.1.2+(uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).1.2+(uniformRunWithFactoryExtras store input hC hAd hm K scalar pc hp).2 ≤156*(uniformPrice m s K store.width store.cap.value) := by
  have he := uniformRun_combined store input hC hAd hm K scalar pc hp
  have ho := uniformRun_work store input hC hAd hm s hs hHeight K scalar pc hp
  simp only [uniformRunWithFactoryExtras_compat,uniformRunWithDrawExtras_compat] at he ⊢
  omega

end GroupDraw

namespace GroupDraw
open BinaryWordGroupDrawMeasured

theorem mixedTwoRun_factory (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤155*(mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2 := by
  have h := mixedTwoRun_combined store input hC hAd K scalar pc hp
  omega

theorem mixedTwoRun_price (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 3 ≤ s) (hHeight : MixedHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2+(mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).1.2+(mixedTwoRunWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤156*(mixedPrice s K store.width store.cap.value) := by
  have he := mixedTwoRun_combined store input hC hAd K scalar pc hp
  have ho := mixedTwoRun_work store input hC hAd s hs hHeight K scalar pc hp
  simp only [mixedTwoRunWithFactoryExtras_compat,mixedTwoRunWithDrawExtras_compat] at he ⊢
  omega

end GroupDraw

end Blotto.BinaryFourGroupFactoryExtras
