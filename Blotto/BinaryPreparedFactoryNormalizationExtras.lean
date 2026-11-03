import Blotto.BinaryNestedFactoryNormalizationExtras
import Blotto.BinaryReflectedTerminalFactoryMeasured
import Blotto.BinaryGroupFactoryMeasured
import Blotto.BinaryReflectedResourceMeasured

/-! Actual higher factories retain only reached normalization fields, without
replaying children. Old result/trace/source records and all original component
price premises remain exact. Complete root/native/physical joins are separate. -/
namespace Blotto.BinaryPreparedFactoryNormalizationExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] BinaryLifetimeArrayExtras.build BinaryReflectedTerminalFactoryMeasured.fromTerminalWithExtras BinaryReflectedTerminalFactoryMeasured.tableWithExtras BinaryReflectedTerminalFactoryMeasured.preparedWithExtras BinaryGroupFactoryMeasured.uniformFactoryWithExtras BinaryGroupFactoryMeasured.uniformPreparedWithExtras BinaryGroupFactoryMeasured.mixedTwoPreparedWithExtras BinaryReflectedResourceMeasured.runWithExtras BinaryNestedBoundaryMeasured.childWithExtras BinaryNestedBoundaryMeasured.boundaryWithExtras BinaryNestedControlMeasured.classifyWithExtras BinaryNestedControlMeasured.interiorWithExtras BinaryNestedControlMeasured.runWithExtras BinaryNestedFirstLocationMeasured.locationWithExtras BinaryNestedFirstDescriptorMeasured.positiveFromWithExtras BinaryNestedFirstDescriptorMeasured.positiveWithExtras BinaryNestedFirstDescriptorMeasured.fromParametersWithExtras BinaryNestedFirstDescriptorMeasured.descriptorWithExtras BinaryNestedFamilyMeasured.prepareWithExtras BinaryNestedFamilyMeasured.fromFamilyWithExtras BinaryNestedFamilyMeasured.lotteryWithExtras BinaryNestedFirstProfileMeasured.profileWithExtras BinaryNestedSecondProfileMeasured.mixWithExtras BinaryNestedSecondProfileMeasured.profileWithExtras BinaryNestedThirdProfileMeasured.mixWithExtras BinaryNestedThirdProfileMeasured.profileWithExtras BinaryNestedProfileMeasured.orderedWithExtras BinaryNestedProfileMeasured.profileWithExtras BinaryThreeFactoryMeasured.orderedWithExtras BinaryThreeFactoryMeasured.descriptorWithExtras BinarySmallUniformDescriptorMeasured.descriptorWithExtras BinarySmallUniformFactoryMeasured.descriptorWithExtras BinaryFourGluingParentsMeasured.runWithExtras BinaryFourGluingMeasured.descriptorWithExtras BinaryNestedSecondUniformMeasured.fromPreparedWithExtras BinaryNestedSecondUniformMeasured.uniformWithExtras BinaryReflectedPreparationMeasured.fromSystemWithExtras BinaryReflectedPreparationMeasured.fromParametersWithExtras BinaryReflectedPreparationMeasured.prepareWithExtras BinaryNestedBinaryAssemblyMeasured.weightsWithExtras BinaryNestedBinaryAssemblyMeasured.fromComplementWithExtras BinaryNestedBinaryAssemblyMeasured.binaryWithExtras BinaryNestedFirstAssemblyMeasured.rowShiftWithExtras BinaryNestedFirstAssemblyMeasured.rowsShiftWithExtras BinaryNestedFirstAssemblyMeasured.shiftWithExtras BinaryNestedOrderMeasured.orderWithExtras BinaryNestedResidualMeasured.environmentWithExtras BinaryNestedResidualMeasured.fromEnvironmentWithExtras BinaryNestedResidualMeasured.residualWithExtras BinaryNestedSecondUniformMeasured.prepareWithExtras BinaryReflectedSystemMeasured.fromParametersWithExtras BinaryReflectedSystemMeasured.capacityWithExtras BinaryReflectedTerminalInputMeasured.terminalWithExtras BinarySmallUniformDescriptorMeasured.childWithExtras BinarySmallUniformPreparationMeasured.prepareWithExtras BinarySmallUniformSplitMeasured.arithmeticWithExtras BinarySmallUniformSplitMeasured.splitWithExtras BinaryQuadraticThreeFactoryMeasured.vertexRowWithExtras BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras BinaryThreeGeometryMeasured.geometryWithExtras BinaryThreeGeometryMeasured.regimeWithExtras BinaryOverlapGluingMeasured.fromEnvironmentWithExtras BinaryOverlapGluingMeasured.slotWithExtras BinaryFourParametersMeasured.prepareWithExtras BinaryNestedParameterMeasured.runProgramsWithExtras BinaryNestedParameterMeasured.prepareAtWithExtras BinaryNestedParameterMeasured.prepareWithExtras BinaryNestedParameterMeasured.geometryWithExtras BinaryNestedResidualDescriptorMeasured.weightsWithExtras BinaryNestedResidualDescriptorMeasured.vertexRowWithExtras BinaryNestedResidualDescriptorMeasured.rowsWithExtras BinaryNestedResidualDescriptorMeasured.descriptorWithExtras BinaryOverlapGluingMeasured.descriptorWithExtras

namespace ReflectedTerminalFactory
open BinaryReflectedTerminalFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem fromTerminal_joint (terminal : (Terminal × Trace) × ℕ) (K : ℕ) (outer : BinaryScalarTape K)
    (E : ℕ) (hE : E ≤ 155*terminal.2) :
    E+(fromTerminalWithExtras terminal K outer).2 ≤ 155*(fromTerminalWithExtras terminal K outer).1.2 := by
  have hn := BinaryNestedFactoryNormalizationExtras.NestedProfile.profile_extra terminal.1.1.1 K outer
  simp only [fromTerminalWithExtras,collect]
  omega

theorem fromTerminal_extra (terminal : (Terminal × Trace) × ℕ) (K : ℕ) (outer : BinaryScalarTape K) :
    (fromTerminalWithExtras terminal K outer).2 ≤ 155*(fromTerminalWithExtras terminal K outer).1.2 := by
  simpa only [Nat.zero_add] using fromTerminal_joint terminal K outer 0 (by omega)

theorem table_extra {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (K : ℕ) (outer : BinaryScalarTape K) :
    (tableWithExtras cached result K outer).2 ≤ 155*(tableWithExtras cached result K outer).1.2 := by
  have h := fromTerminal_joint (BinaryReflectedTerminalInputMeasured.terminalWithExtras cached result.state).1 K outer
    (BinaryReflectedTerminalInputMeasured.terminalWithExtras cached result.state).2
    (BinaryDirectFactoryNormalizationExtras.ReflectedTerminalInput.terminal_extra cached result.state)
  simpa only [tableWithExtras] using h

theorem prepared_extra (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) :
    (preparedWithExtras input hC hAd cached N bits result hSuccess K outer).2 ≤ 155*(preparedWithExtras input hC hAd cached N bits result hSuccess K outer).1.2 := by
  have h := table_extra cached result K outer
  simp only [preparedWithExtras,attach]
  exact h

theorem fromTerminal_price (terminal : (Terminal × Trace) × ℕ) (hC : terminal.1.1.1.Canonical) (H : ℕ) (hs : 3 ≤ H)
    (hHeight : BinaryNestedParameterWork.InputHeight terminal.1.1.1 H) (K : ℕ) (outer : BinaryScalarTape K)
    (P U : ℕ) (hTerminal : terminal.2 ≤ P ∧ usage terminal.1.2 ≤ U) :
    (fromTerminalWithExtras terminal K outer).1.2+(fromTerminalWithExtras terminal K outer).2 ≤ 156*(P+BinaryNestedProfileMeasured.workEnvelope H K+85000+12) ∧
      usage (fromTerminalWithExtras terminal K outer).1.1.2 ≤ U+BinaryNestedProfileMeasured.envelope H K+50000+64 := by
  have he := fromTerminal_extra terminal K outer
  have ho := fromTerminal_bounds terminal hC H hs hHeight K outer P U hTerminal
  simp only [fromTerminalWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem table_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K) :
    (tableWithExtras cached result K outer).1.2+(tableWithExtras cached result K outer).2 ≤ 156*(workEnvelope s K) ∧ usage (tableWithExtras cached result K outer).1.1.2 ≤ envelope s K := by
  have he := table_extra cached result K outer
  have ho := table_bounds input source hC hR hCase s hs hH N bits result hSuccess cached K outer
  simp only [tableWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem prepared_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : BinaryReflectedSerialRun.Admissible input)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result)
    (cached : BinaryReflectedPreparationLifetime.Prepared input) (K : ℕ) (outer : BinaryScalarTape K) :
    (preparedWithExtras input hC hAd cached N bits result hSuccess K outer).1.2+(preparedWithExtras input hC hAd cached N bits result hSuccess K outer).2 ≤ 156*(workEnvelope s K) ∧
      usage (preparedWithExtras input hC hAd cached N bits result hSuccess K outer).1.1.2 ≤ envelope s K := by
  have he := prepared_extra input hC hAd cached N bits result hSuccess K outer
  have ho := prepared_bounds input source hC hR hCase hAd s hs hH N bits result hSuccess cached K outer
  simp only [preparedWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end ReflectedTerminalFactory

namespace GroupFactory
open BinaryGroupFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork

theorem uniformFactory_extra {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    (uniformFactoryWithExtras input hm).2 ≤ 155*(uniformFactoryWithExtras input hm).1.2 := by
  rcases hm with rfl | rfl
  · simp only [uniformFactoryWithExtras,show (2 : ℕ) = 2 from rfl,dif_pos]
    omega
  · have h := BinaryHigherFactoryNormalizationExtras.ThreeFactory.descriptor_extra (uniformThree input)
    simp only [uniformFactoryWithExtras,dif_neg (by decide : ¬(3 : ℕ) = 2)]
    omega

theorem uniformPrepared_extra {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) :
    (uniformPreparedWithExtras input hC hAd hm).2 ≤ 155*(uniformPreparedWithExtras input hC hAd hm).1.2 := by
  have h := uniformFactory_extra input hm
  simp only [uniformPreparedWithExtras]
  omega

theorem mixedTwoPrepared_extra (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    (mixedTwoPreparedWithExtras input hC hAd).2 ≤ 155*(mixedTwoPreparedWithExtras input hC hAd).1.2 := by
  have h := BinaryHigherFactoryNormalizationExtras.ThreeFactory.descriptor_extra (mixedThree input)
  simp only [mixedTwoPreparedWithExtras]
  omega

theorem uniformFactory_price {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hm : m = 2 ∨ m = 3)
    (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s) :
    (uniformFactoryWithExtras input hm).1.2+(uniformFactoryWithExtras input hm).2 ≤ 156*(workEnvelope s) ∧ usage (uniformFactoryWithExtras input hm).1.1.2 ≤ envelope s := by
  have he := uniformFactory_extra input hm
  have ho := uniformFactory_bounds input hC hm s hs hH
  simp only [uniformFactoryWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem uniformPrepared_price {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s) (hH : UniformHeights input s) :
    (uniformPreparedWithExtras input hC hAd hm).1.2+(uniformPreparedWithExtras input hC hAd hm).2 ≤ 156*(workEnvelope s+4) ∧
      usage (uniformPreparedWithExtras input hC hAd hm).1.1.2 ≤ envelope s+20 := by
  have he := uniformPrepared_extra input hC hAd hm
  have ho := uniformPrepared_bounds input hC hAd hm s hs hH
  simp only [uniformPreparedWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem mixedTwoPrepared_price (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input)
    (s : ℕ) (hs : 3 ≤ s) (hH : MixedHeights input s) :
    (mixedTwoPreparedWithExtras input hC hAd).1.2+(mixedTwoPreparedWithExtras input hC hAd).2 ≤ 156*(workEnvelope s) ∧
      usage (mixedTwoPreparedWithExtras input hC hAd).1.1.2 ≤ envelope s := by
  have he := mixedTwoPrepared_extra input hC hAd
  have ho := mixedTwoPrepared_bounds input hC hAd s hs hH
  simp only [mixedTwoPreparedWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end GroupFactory

namespace ReflectedResource
open BinaryReflectedResourceMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryPRGHeapTraceUsage BinaryReflectedPreparationLifetime
open BinaryPRGWordControllerBooleanResourceThreeBridge

theorem run_extra (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runWithExtras seed input hC pc hp).2 ≤ 155*(runWithExtras seed input hC pc hp).1.2 := by
  have h := BinaryHigherFactoryNormalizationExtras.ReflectedPreparation.prepare_extra input hC
  simp only [runWithExtras,join]
  omega

theorem run_price (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runWithExtras seed input hC pc hp).1.2+(runWithExtras seed input hC pc hp).2 ≤ 156*(workEnvelope s seed.width seed.cap.value) ∧
      usage (runWithExtras seed input hC pc hp).1.1.2 ≤ envelope s seed.width seed.cap.value := by
  have he := run_extra seed input hC pc hp
  have ho := run_bounds seed input source hC hR hCase s hs hH pc hp
  simp only [runWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end ReflectedResource

end Blotto.BinaryPreparedFactoryNormalizationExtras
