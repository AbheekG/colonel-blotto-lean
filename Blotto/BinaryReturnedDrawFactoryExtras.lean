import Blotto.BinaryPreparedFactoryNormalizationExtras
import Blotto.BinaryReturnedTerminalDrawExtras

/-! Actual factory fields and the preceding draw fields fit disjoint reached
source components. Every old value/trace/source/draw record remains exact.
Full native counter/ownership/physical costs and root joins remain separate. -/
namespace Blotto.BinaryReturnedDrawFactoryExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryReflectedFourSetup
open BinaryReflectedDrawMeasured (Reached)
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] BinaryFourGluingDrawMeasured.preparedWithExtras BinaryFourGluingDrawMeasured.runWithFactoryExtras BinaryFourSmallUniformDrawMeasured.preparedWithExtras BinaryFourSmallUniformDrawMeasured.runWithFactoryExtras BinaryReflectedDrawMeasured.afterResourceWithFactoryExtras BinaryReflectedDrawMeasured.fromReachedWithFactoryExtras BinaryReflectedDrawMeasured.runWithFactoryExtras BinaryWordSegmentMeasured.runWithExtras BinaryReflectedTableDrawMeasured.runWithExtras BinaryReflectedTerminalFactoryMeasured.preparedWithExtras BinaryReflectedResourceMeasured.runWithExtras

namespace Gluing
open BinaryFourGluingDrawMeasured

theorem prepared_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) :
    (preparedWithExtras input hC hAd).2 ≤155*(preparedWithExtras input hC hAd).1.2 := by
  have h := BinaryHigherFactoryNormalizationExtras.FourGluing.descriptor_extra input hC
  simp only [preparedWithExtras]
  omega

theorem run_combined (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2 := by
  have hPrepared := prepared_bound input hC hAd
  have hd := BinaryReturnedCategoricalExtras.segment_bound store (preparedWithExtras input hC hAd).1.1.1 0 K scalar pc hp
  simp only [runWithFactoryExtras]
  omega

theorem run_factory (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2 := by
  have h := run_combined store input hC hAd K scalar pc hp
  omega

theorem run_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (hAd : BinaryGluingSampler.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤156*(workEnvelope s K store.width store.cap.value) ∧
      usage (runWithFactoryExtras store input hC hAd K scalar pc hp).1.1.1.2 ≤ envelope s K store.width store.cap.value := by
  have he := run_combined store input hC hAd K scalar pc hp
  have ho := run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp
  simp only [runWithFactoryExtras_compat,runWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem prepared_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (hAd : BinaryGluingSampler.Admissible input) :
    (preparedWithExtras input hC hAd).1.2+(preparedWithExtras input hC hAd).2 ≤156*(BinaryFourGluingMeasured.workEnvelope s+4) ∧ usage (preparedWithExtras input hC hAd).1.1.2 ≤ BinaryFourGluingMeasured.envelope s := by
  have he := prepared_bound input hC hAd
  have ho := BinaryFourGluingMeasured.descriptor_bounds input source hC hR hCase s hs hH
  simp only [preparedWithExtras_compat,prepared_record] at he ⊢
  exact ⟨by omega,ho.2⟩

end Gluing

namespace SmallUniform
open BinaryFourSmallUniformDrawMeasured

theorem prepared_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) :
    (preparedWithExtras input hC hAd).2 ≤155*(preparedWithExtras input hC hAd).1.2 := by
  have h := BinaryHigherFactoryNormalizationExtras.SmallUniformFactory.descriptor_extra input
  simp only [preparedWithExtras]
  omega

theorem run_combined (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2 := by
  have hPrepared := prepared_bound input hC hAd
  have hd := BinaryReturnedCategoricalExtras.segment_bound store (preparedWithExtras input hC hAd).1.1.1 0 K scalar pc hp
  simp only [runWithFactoryExtras]
  omega

theorem run_factory (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2 := by
  have h := run_combined store input hC hAd K scalar pc hp
  omega

theorem run_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (hAd : BinarySmallRootSample.Admissible input) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K scalar pc hp).2 ≤156*(workEnvelope s K store.width store.cap.value) ∧
      usage (runWithFactoryExtras store input hC hAd K scalar pc hp).1.1.1.2 ≤ envelope s K store.width store.cap.value := by
  have he := run_combined store input hC hAd K scalar pc hp
  have ho := run_bounds store input source hC hR hCase hAd s hs hH K scalar pc hp
  simp only [runWithFactoryExtras_compat,runWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem prepared_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) (hAd : BinarySmallRootSample.Admissible input) :
    (preparedWithExtras input hC hAd).1.2+(preparedWithExtras input hC hAd).2 ≤156*(BinarySmallUniformFactoryMeasured.workEnvelope s+4) ∧ usage (preparedWithExtras input hC hAd).1.1.2 ≤ BinarySmallUniformFactoryMeasured.envelope s := by
  have he := prepared_bound input hC hAd
  have ho := BinarySmallUniformFactoryMeasured.descriptor_bounds input source hC hR hCase s hs hH
  simp only [preparedWithExtras_compat,prepared_record] at he ⊢
  exact ⟨by omega,ho.2⟩

end SmallUniform

namespace Reflected
open BinaryReflectedDrawMeasured

theorem after_combined (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).1.2+(afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).2 ≤155*(afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).1.1.2 := by
  simp only [afterResourceWithFactoryExtras]
  split
  · change (0 : ℕ)+0 ≤155*4
    omega
  · rename_i result hResult
    have hSuccess := BinaryPRGWordControllerReflected.setup_local_success store input hC pc hp result (by rw [← hResource]; exact hResult)
    let prepared := BinaryReflectedTerminalFactoryMeasured.preparedWithExtras input hC hAd cached
      (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
    have ht := BinaryPreparedFactoryNormalizationExtras.ReflectedTerminalFactory.prepared_extra input hC hAd cached
      (store.cap.value-pc.value) (BinaryPRGWordControllerReflected.localReader store pc hp) result hSuccess K outer
    have hd := BinaryReturnedReflectedExtras.table_bound store input prepared.1.1.1 K scalar resource.2
      (by rw [hResource]; exact (BinaryPRGWordControllerThreeResource.setupIndexed_position store input hC pc hp).2)
    simp only [prepared] at hd
    dsimp only
    omega

theorem reached_joint (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) (E : ℕ) (hE : E ≤155*reached.2) :
    E+(fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1.2+(fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).2 ≤155*(fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1.1.2 := by
  have ha := after_combined store input hC hAd reached.1.1.1 pc hp reached.1.1.2 hResource K outer scalar
  simp only [fromReachedWithFactoryExtras,join]
  omega

theorem reached_combined (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) :
    (fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1.2+(fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).2 ≤155*(fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1.1.2 := by
  simpa only [Nat.zero_add] using reached_joint store input hC hAd K outer scalar pc hp reached hResource 0 (by omega)

theorem run_combined (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2 := by
  have hPrefix := BinaryPreparedFactoryNormalizationExtras.ReflectedResource.run_extra store input hC pc hp
  have h := reached_joint store input hC hAd K outer scalar pc hp (BinaryReflectedResourceMeasured.runWithExtras store input hC pc hp).1
    (by simpa only [BinaryReflectedResourceMeasured.runWithExtras_compat] using BinaryReflectedResourceMeasured.run_resource store input hC pc hp)
    (BinaryReflectedResourceMeasured.runWithExtras store input hC pc hp).2 hPrefix
  simp only [runWithFactoryExtras]
  omega

theorem afterResource_factory (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).2 ≤155*(afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).1.1.2 := by
  have h := after_combined store input hC hAd cached pc hp resource hResource K outer scalar
  omega

theorem afterResource_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).1.1.2+(afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).1.2+(afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).2 ≤156*(afterPrice s K store.width store.cap.value) ∧
      usage (afterResourceWithFactoryExtras store input hC hAd cached pc hp resource hResource K outer scalar).1.1.1.2 ≤ afterEnvelope s K store.width store.cap.value := by
  have he := after_combined store input hC hAd cached pc hp resource hResource K outer scalar
  have ho := afterResource_bounds store input source hC hR hCase hAd s hs hH cached pc hp resource hResource K outer scalar
  simp only [afterResourceWithFactoryExtras_compat,afterResourceWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem fromReached_factory (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp) :
    (fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).2 ≤155*(fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1.1.2 := by
  have h := reached_combined store input hC hAd K outer scalar pc hp reached hResource
  omega

theorem fromReached_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (reached : Reached store input)
    (hResource : reached.1.1.2 = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (hReached : reached.2 ≤ BinaryReflectedResourceMeasured.workEnvelope s store.width store.cap.value ∧
      usage reached.1.2 ≤ BinaryReflectedResourceMeasured.envelope s store.width store.cap.value) :
    (fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1.1.2+(fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1.2+(fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).2 ≤156*(workEnvelope s K store.width store.cap.value) ∧
      usage (fromReachedWithFactoryExtras store input hC hAd K outer scalar pc hp reached hResource).1.1.1.2 ≤ envelope s K store.width store.cap.value := by
  have he := reached_combined store input hC hAd K outer scalar pc hp reached hResource
  have ho := fromReached_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp reached hResource hReached
  simp only [fromReachedWithFactoryExtras_compat,fromReachedWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem run_factory (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤155*(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2 := by
  have h := run_combined store input hC hAd K outer scalar pc hp
  omega

theorem run_price (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.2+(runWithFactoryExtras store input hC hAd K outer scalar pc hp).2 ≤156*(workEnvelope s K store.width store.cap.value) ∧
      usage (runWithFactoryExtras store input hC hAd K outer scalar pc hp).1.1.1.2 ≤ envelope s K store.width store.cap.value := by
  have he := run_combined store input hC hAd K outer scalar pc hp
  have ho := run_bounds store input source hC hR hCase hAd s hs hH K outer scalar pc hp
  simp only [runWithFactoryExtras_compat,runWithDrawExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end Reflected

end Blotto.BinaryReturnedDrawFactoryExtras
