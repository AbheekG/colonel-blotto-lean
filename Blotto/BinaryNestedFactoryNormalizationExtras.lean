import Blotto.BinaryHigherFactoryNormalizationExtras
import Blotto.BinaryNestedBoundaryMeasured
import Blotto.BinaryNestedControlMeasured
import Blotto.BinaryNestedFirstLocationMeasured
import Blotto.BinaryNestedFirstDescriptorMeasured
import Blotto.BinaryNestedFamilyMeasured
import Blotto.BinaryNestedFirstProfileMeasured
import Blotto.BinaryNestedSecondProfileMeasured
import Blotto.BinaryNestedThirdProfileMeasured
import Blotto.BinaryNestedProfileMeasured

/-! Actual higher factories retain only reached normalization fields, without
replaying children. Old result/trace/source records and all original component
price premises remain exact. Complete root/native/physical joins are separate. -/
namespace Blotto.BinaryNestedFactoryNormalizationExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] BinaryLifetimeArrayExtras.build BinaryNestedBoundaryMeasured.childWithExtras BinaryNestedBoundaryMeasured.boundaryWithExtras BinaryNestedControlMeasured.classifyWithExtras BinaryNestedControlMeasured.interiorWithExtras BinaryNestedControlMeasured.runWithExtras BinaryNestedFirstLocationMeasured.locationWithExtras BinaryNestedFirstDescriptorMeasured.positiveFromWithExtras BinaryNestedFirstDescriptorMeasured.positiveWithExtras BinaryNestedFirstDescriptorMeasured.fromParametersWithExtras BinaryNestedFirstDescriptorMeasured.descriptorWithExtras BinaryNestedFamilyMeasured.prepareWithExtras BinaryNestedFamilyMeasured.fromFamilyWithExtras BinaryNestedFamilyMeasured.lotteryWithExtras BinaryNestedFirstProfileMeasured.profileWithExtras BinaryNestedSecondProfileMeasured.mixWithExtras BinaryNestedSecondProfileMeasured.profileWithExtras BinaryNestedThirdProfileMeasured.mixWithExtras BinaryNestedThirdProfileMeasured.profileWithExtras BinaryNestedProfileMeasured.orderedWithExtras BinaryNestedProfileMeasured.profileWithExtras BinaryThreeFactoryMeasured.orderedWithExtras BinaryThreeFactoryMeasured.descriptorWithExtras BinarySmallUniformDescriptorMeasured.descriptorWithExtras BinarySmallUniformFactoryMeasured.descriptorWithExtras BinaryFourGluingParentsMeasured.runWithExtras BinaryFourGluingMeasured.descriptorWithExtras BinaryNestedSecondUniformMeasured.fromPreparedWithExtras BinaryNestedSecondUniformMeasured.uniformWithExtras BinaryReflectedPreparationMeasured.fromSystemWithExtras BinaryReflectedPreparationMeasured.fromParametersWithExtras BinaryReflectedPreparationMeasured.prepareWithExtras BinaryNestedBinaryAssemblyMeasured.weightsWithExtras BinaryNestedBinaryAssemblyMeasured.fromComplementWithExtras BinaryNestedBinaryAssemblyMeasured.binaryWithExtras BinaryNestedFirstAssemblyMeasured.rowShiftWithExtras BinaryNestedFirstAssemblyMeasured.rowsShiftWithExtras BinaryNestedFirstAssemblyMeasured.shiftWithExtras BinaryNestedOrderMeasured.orderWithExtras BinaryNestedResidualMeasured.environmentWithExtras BinaryNestedResidualMeasured.fromEnvironmentWithExtras BinaryNestedResidualMeasured.residualWithExtras BinaryNestedSecondUniformMeasured.prepareWithExtras BinaryReflectedSystemMeasured.fromParametersWithExtras BinaryReflectedSystemMeasured.capacityWithExtras BinaryReflectedTerminalInputMeasured.terminalWithExtras BinarySmallUniformDescriptorMeasured.childWithExtras BinarySmallUniformPreparationMeasured.prepareWithExtras BinarySmallUniformSplitMeasured.arithmeticWithExtras BinarySmallUniformSplitMeasured.splitWithExtras BinaryQuadraticThreeFactoryMeasured.vertexRowWithExtras BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras BinaryThreeGeometryMeasured.geometryWithExtras BinaryThreeGeometryMeasured.regimeWithExtras BinaryOverlapGluingMeasured.fromEnvironmentWithExtras BinaryOverlapGluingMeasured.slotWithExtras BinaryFourParametersMeasured.prepareWithExtras BinaryNestedParameterMeasured.runProgramsWithExtras BinaryNestedParameterMeasured.prepareAtWithExtras BinaryNestedParameterMeasured.prepareWithExtras BinaryNestedParameterMeasured.geometryWithExtras BinaryNestedResidualDescriptorMeasured.weightsWithExtras BinaryNestedResidualDescriptorMeasured.vertexRowWithExtras BinaryNestedResidualDescriptorMeasured.rowsWithExtras BinaryNestedResidualDescriptorMeasured.descriptorWithExtras BinaryOverlapGluingMeasured.descriptorWithExtras

namespace NestedBoundary
open BinaryNestedBoundaryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem child_extra (input : BinaryThreeInputCompiler.Input) :
    (childWithExtras input).2 ≤ 155*(childWithExtras input).1.2 := by
  have h := BinaryHigherFactoryNormalizationExtras.ThreeFactory.descriptor_extra input
  simp only [childWithExtras,childFrom]
  omega

theorem boundary_extra (input : Input) :
    (boundaryWithExtras input).2 ≤ 155*(boundaryWithExtras input).1.2 := by
  have hl := child_extra (BinaryNestedSpecProfile.longInput input)
  have hs := child_extra (BinaryNestedSpecProfile.shortInput input)
  simp only [boundaryWithExtras]
  split_ifs <;> simp only <;> omega

theorem child_price (input : BinaryThreeInputCompiler.Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    (childWithExtras input).1.2+(childWithExtras input).2 ≤ 156*(childPrice s) ∧ usage (childWithExtras input).1.1.2 ≤ childEnvelope s := by
  have he := child_extra input
  have ho := child_bounds input hC s hs hH
  simp only [childWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem boundary_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (boundaryWithExtras input).1.2+(boundaryWithExtras input).2 ≤ 156*(workEnvelope s) ∧ usage (boundaryWithExtras input).1.1.2 ≤ envelope s := by
  have he := boundary_extra input
  have ho := boundary_bounds input hC s hs hH
  simp only [boundaryWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedBoundary

namespace NestedControl
open BinaryNestedControlMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem classify_extra (input : Input) :
    (classifyWithExtras input).2 ≤ 155*(classifyWithExtras input).1.2 := by
  have hb := NestedBoundary.boundary_extra input
  have ho := BinaryDirectFactoryNormalizationExtras.NestedOrder.order_extra input
  simp only [classifyWithExtras]
  split <;> simp only <;> omega

theorem interior_extra (input : Input) :
    (interiorWithExtras input).2 ≤ 155*(interiorWithExtras input).1.2 := by
  have hc := classify_extra input
  simp only [interiorWithExtras]
  split
  · dsimp only; omega
  · rename_i ordered h
    have hp := BinaryFactoryExpressionExtras.NestedParameters.prepare_extra ordered.1
    dsimp only
    omega

theorem run_extra (input : Input) :
    (runWithExtras input).2 ≤ 155*(runWithExtras input).1.2 := by
  have hp := interior_extra input
  simp only [runWithExtras]
  split <;> simp only <;> omega

theorem classify_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (classifyWithExtras input).1.2+(classifyWithExtras input).2 ≤ 156*(classifyPrice s) ∧ usage (classifyWithExtras input).1.1.2 ≤ classifyEnvelope s := by
  have he := classify_extra input
  have ho := classify_bounds input hC s hs hH
  simp only [classifyWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem interior_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (interiorWithExtras input).1.2+(interiorWithExtras input).2 ≤ 156*(interiorPrice s) ∧ usage (interiorWithExtras input).1.1.2 ≤ interiorEnvelope s := by
  have he := interior_extra input
  have ho := interior_bounds input hC s hs hH
  simp only [interiorWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem run_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (runWithExtras input).1.2+(runWithExtras input).2 ≤ 156*(workEnvelope s) ∧ usage (runWithExtras input).1.1.2 ≤ envelope s := by
  have he := run_extra input
  have ho := run_bounds input hC s hs hH
  simp only [runWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedControl

namespace NestedFirstLocation
open BinaryNestedFirstLocationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem location_extra (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (locationWithExtras input K bits).2 ≤ 155*(locationWithExtras input K bits).1.2 := by
  have hp := BinaryFactoryExpressionExtras.NestedParameters.prepareAt_extra input (BinaryNestedFirstLocationMeasured.midpoint K bits).1.1
  simp only [locationWithExtras,collect]
  omega

theorem location_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (locationWithExtras input K bits).1.2+(locationWithExtras input K bits).2 ≤ 156*(workEnvelope s K) ∧ usage (locationWithExtras input K bits).1.1.2 ≤ envelope s K := by
  have he := location_extra input K bits
  have ho := location_bounds input hC s hs hH K bits
  simp only [locationWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedFirstLocation

namespace NestedFirstDescriptor
open BinaryNestedFirstDescriptorMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem positiveFrom_joint (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (x : SignedWord)
    (E : ℕ) (hE : E ≤ 155*geometry.2) :
    E+(positiveFromWithExtras geometry x).2 ≤ 155*(positiveFromWithExtras geometry x).1.2 := by
  have ht := BinaryFactoryExpressionExtras.ThreeFactory.descriptor_extra geometry.1.1
  have hs := BinaryDirectFactoryNormalizationExtras.NestedFirstAssembly.shift_extra (BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras geometry.1.1).1.1.1 x
  simp only [positiveFromWithExtras,joinPositive]
  omega

theorem positiveFrom_extra (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (x : SignedWord) :
    (positiveFromWithExtras geometry x).2 ≤ 155*(positiveFromWithExtras geometry x).1.2 := by
  simpa only [Nat.zero_add] using positiveFrom_joint geometry x 0 (by omega)

theorem positive_extra (input : Input) (x : SignedWord) :
    (positiveWithExtras input x).2 ≤ 155*(positiveWithExtras input x).1.2 := by
  have h := positiveFrom_joint (BinaryNestedParameterMeasured.geometryWithExtras input x).1 x
    (BinaryNestedParameterMeasured.geometryWithExtras input x).2 (BinaryFactoryExpressionExtras.NestedParameters.geometry_extra input x)
  simpa only [positiveWithExtras] using h

theorem fromParameters_joint (input : Input) (x : SignedWord)
    (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) (E : ℕ) (hE : E ≤ 155*parameters.2) :
    E+(fromParametersWithExtras input x parameters).2 ≤ 155*(fromParametersWithExtras input x parameters).1.2 := by
  have hp := positive_extra input x
  simp only [fromParametersWithExtras]
  split_ifs <;> omega

theorem fromParameters_extra (input : Input) (x : SignedWord) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) :
    (fromParametersWithExtras input x parameters).2 ≤ 155*(fromParametersWithExtras input x parameters).1.2 := by
  simpa only [Nat.zero_add] using fromParameters_joint input x parameters 0 (by omega)

theorem descriptor_extra (input : Input) (x : SignedWord) :
    (descriptorWithExtras input x).2 ≤ 155*(descriptorWithExtras input x).1.2 := by
  have h := fromParameters_joint input x (BinaryNestedParameterMeasured.prepareAtWithExtras input x).1
    (BinaryNestedParameterMeasured.prepareAtWithExtras input x).2 (BinaryFactoryExpressionExtras.NestedParameters.prepareAt_extra input x)
  simpa only [descriptorWithExtras] using h

theorem positiveFrom_price (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (x : SignedWord)
    (hC : ∀ j,CanonicalWord (geometry.1.1.read j)) (H : ℕ) (hH : 3 ≤ H)
    (hHeight : BinarySyntaxUniformWork.EnvHeight geometry.1.1 H) (hX : width x ≤ shiftWidth H)
    (G U : ℕ) (hGeometry : geometry.2 ≤ G ∧ usage geometry.1.2 ≤ U) :
    (positiveFromWithExtras geometry x).1.2+(positiveFromWithExtras geometry x).2 ≤ 156*(G+BinaryQuadraticThreeFactoryMeasured.workEnvelope H+
      BinaryNestedFirstAssemblyMeasured.shiftPrice (shiftWidth H)+12) ∧
    usage (positiveFromWithExtras geometry x).1.1.2 ≤ U+BinaryQuadraticThreeFactoryMeasured.envelope H+
      BinaryNestedFirstAssemblyMeasured.shiftEnvelope (shiftWidth H)+64 := by
  have he := positiveFrom_extra geometry x
  have ho := positiveFrom_bounds geometry x hC H hH hHeight hX G U hGeometry
  simp only [positiveFromWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem positive_price (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s) :
    (positiveWithExtras input x).1.2+(positiveWithExtras input x).2 ≤ 156*(positivePrice s) ∧ usage (positiveWithExtras input x).1.1.2 ≤ positiveEnvelope s := by
  have he := positive_extra input x
  have ho := positive_bounds input x hC hX s hs hH hXH
  simp only [positiveWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem fromParameters_price (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s)
    (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ)
    (hPC : CanonicalWord (parameters.1.1.read 4))
    (hPH : RationalHeight (value (parameters.1.1.read 4)) (expressionHeightBudget s 16))
    (hP : parameters.2 ≤ BinaryNestedParameterMeasured.workEnvelope 9 s ∧
      usage parameters.1.2 ≤ BinaryNestedParameterMeasured.envelope 9 s 128 10) :
    (fromParametersWithExtras input x parameters).1.2+(fromParametersWithExtras input x parameters).2 ≤ 156*(workEnvelope s) ∧ usage (fromParametersWithExtras input x parameters).1.1.2 ≤ envelope s := by
  have he := fromParameters_extra input x parameters
  have ho := fromParameters_bounds input x hC hX s hs hH hXH parameters hPC hPH hP
  simp only [fromParametersWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem descriptor_price (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s) :
    (descriptorWithExtras input x).1.2+(descriptorWithExtras input x).2 ≤ 156*(workEnvelope s) ∧ usage (descriptorWithExtras input x).1.1.2 ≤ envelope s := by
  have he := descriptor_extra input x
  have ho := descriptor_bounds input x hC hX s hs hH hXH
  simp only [descriptorWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedFirstDescriptor

namespace NestedFamily
open BinaryNestedFamilyMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem prepare_extra (input : Input) (length : SignedWord) :
    (prepareWithExtras input length).2 ≤ 155*(prepareWithExtras input length).1.2 := by
  have hp := BinaryFactoryExpressionExtras.NestedParameters.prepareAt_extra input length
  simp only [prepareWithExtras,inputFrom]
  omega

theorem fromFamily_joint (family : (Input × Trace) × ℕ) (K : ℕ) (bits : BinaryScalarTape K)
    (E : ℕ) (hE : E ≤ 155*family.2) :
    E+(fromFamilyWithExtras family K bits).2 ≤ 155*(fromFamilyWithExtras family K bits).1.2 := by
  have hl := NestedFirstLocation.location_extra family.1.1 K bits
  have hd := NestedFirstDescriptor.descriptor_extra family.1.1 (BinaryNestedFirstLocationMeasured.locationWithExtras family.1.1 K bits).1.1.1
  simp only [fromFamilyWithExtras,collect]
  omega

theorem fromFamily_extra (family : (Input × Trace) × ℕ) (K : ℕ) (bits : BinaryScalarTape K) :
    (fromFamilyWithExtras family K bits).2 ≤ 155*(fromFamilyWithExtras family K bits).1.2 := by
  simpa only [Nat.zero_add] using fromFamily_joint family K bits 0 (by omega)

theorem lottery_extra (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (lotteryWithExtras input length K bits).2 ≤ 155*(lotteryWithExtras input length K bits).1.2 := by
  have h := fromFamily_joint (prepareWithExtras input length).1 K bits (prepareWithExtras input length).2 (prepare_extra input length)
  simpa only [lotteryWithExtras] using h

theorem prepare_price (input : Input) (length : SignedWord) (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hLength : RationalHeight (value length) s) :
    (prepareWithExtras input length).1.2+(prepareWithExtras input length).2 ≤ 156*(inputPrice s) ∧ usage (prepareWithExtras input length).1.1.2 ≤ inputEnvelope s := by
  have he := prepare_extra input length
  have ho := prepare_bounds input length hC hL s hs hH hLength
  simp only [prepareWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem fromFamily_price (family : (Input × Trace) × ℕ) (hC : family.1.1.Canonical)
    (H : ℕ) (hH : 3 ≤ H) (hHeight : BinaryNestedParameterWork.InputHeight family.1.1 H)
    (K : ℕ) (bits : BinaryScalarTape K) (G U : ℕ) (hFamily : family.2 ≤ G ∧ usage family.1.2 ≤ U) :
    (fromFamilyWithExtras family K bits).1.2+(fromFamilyWithExtras family K bits).2 ≤ 156*(G+BinaryNestedFirstLocationMeasured.workEnvelope H K+
      BinaryNestedFirstDescriptorMeasured.workEnvelope (expressionHeightBudget (max H (K+2)) 16)+12) ∧
    usage (fromFamilyWithExtras family K bits).1.1.2 ≤ U+BinaryNestedFirstLocationMeasured.envelope H K+
      BinaryNestedFirstDescriptorMeasured.envelope (expressionHeightBudget (max H (K+2)) 16)+64 := by
  have he := fromFamily_extra family K bits
  have ho := fromFamily_bounds family hC H hH hHeight K bits G U hFamily
  simp only [fromFamilyWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem lottery_price (input : Input) (length : SignedWord) (hC : input.Canonical) (hL : CanonicalWord length)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hLength : RationalHeight (value length) s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (lotteryWithExtras input length K bits).1.2+(lotteryWithExtras input length K bits).2 ≤ 156*(workEnvelope s K) ∧ usage (lotteryWithExtras input length K bits).1.1.2 ≤ envelope s K := by
  have he := lottery_extra input length K bits
  have ho := lottery_bounds input length hC hL s hs hH hLength K bits
  simp only [lotteryWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedFamily

namespace NestedFirstProfile
open BinaryNestedFirstProfileMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem profile_extra (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input K bits).2 ≤ 155*(profileWithExtras input K bits).1.2 := by
  have hl := NestedFirstLocation.location_extra input K bits
  have hd := NestedFirstDescriptor.descriptor_extra input (BinaryNestedFirstLocationMeasured.locationWithExtras input K bits).1.1.1
  simp only [profileWithExtras,collect]
  omega

theorem profile_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input K bits).1.2+(profileWithExtras input K bits).2 ≤ 156*(workEnvelope s K) ∧ usage (profileWithExtras input K bits).1.1.2 ≤ envelope s K := by
  have he := profile_extra input K bits
  have ho := profile_bounds input hC s hs hH K bits
  simp only [profileWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedFirstProfile

namespace NestedSecondProfile
open BinaryNestedSecondProfileMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem mix_joint (alpha : SignedWord) (family : Small) (uniform : (Small × Trace) × ℕ)
    (E : ℕ) (hE : E ≤ 155*uniform.2) :
    E+(mixWithExtras alpha family uniform).2 ≤ 155*(mixWithExtras alpha family uniform).1.2 := by
  have ha := BinaryDirectFactoryNormalizationExtras.NestedBinaryAssembly.binary_extra alpha family uniform.1.1
  simp only [mixWithExtras]
  omega

theorem mix_extra (alpha : SignedWord) (family : Small) (uniform : (Small × Trace) × ℕ) :
    (mixWithExtras alpha family uniform).2 ≤ 155*(mixWithExtras alpha family uniform).1.2 := by
  simpa only [Nat.zero_add] using mix_joint alpha family uniform 0 (by omega)

theorem profile_extra (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input parameters K bits).2 ≤ 155*(profileWithExtras input parameters K bits).1.2 := by
  let family := BinaryNestedFamilyMeasured.lotteryWithExtras input (parameters.read 6) K bits
  let uniform := BinaryNestedSecondUniformMeasured.uniformWithExtras input (parameters.read 6)
  have hf := NestedFamily.lottery_extra input (parameters.read 6) K bits
  have hu := BinaryHigherFactoryNormalizationExtras.NestedSecondUniform.uniform_extra input (parameters.read 6)
  have hm := mix_joint (parameters.read 7) family.1.1.1 uniform.1 uniform.2 hu
  simp only [family,uniform] at hm
  simp only [profileWithExtras]
  split_ifs <;> simp only <;> omega

theorem mix_price (alpha : SignedWord) (family : Small) (uniform : (Small × Trace) × ℕ) (hA : CanonicalWord alpha)
    (W : ℕ) (hW : 1 ≤ W) (hAlpha : width alpha ≤ W)
    (hFirst : ∀ j,width (family.weight.read j) ≤ W) (hSecond : ∀ j,width (uniform.1.1.weight.read j) ≤ W)
    (P U : ℕ) (hUniform : uniform.2 ≤ P ∧ usage uniform.1.2 ≤ U) :
    (mixWithExtras alpha family uniform).1.2+(mixWithExtras alpha family uniform).2 ≤ 156*(P+BinaryNestedBinaryAssemblyMeasured.workEnvelope W+8) ∧
    usage (mixWithExtras alpha family uniform).1.1.2 ≤ U+BinaryNestedBinaryAssemblyMeasured.envelope W+64 := by
  have he := mix_extra alpha family uniform
  have ho := mix_bounds alpha family uniform hA W hW hAlpha hFirst hSecond P U hUniform
  simp only [mixWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem profile_price (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input parameters K bits).1.2+(profileWithExtras input parameters K bits).2 ≤ 156*(workEnvelope s K) ∧ usage (profileWithExtras input parameters K bits).1.1.2 ≤ envelope s K := by
  have he := profile_extra input parameters K bits
  have ho := profile_bounds input parameters hC hParameters s hs hH K bits
  simp only [profileWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedSecondProfile

namespace NestedThirdProfile
open BinaryNestedThirdProfileMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem mix_joint (alpha : SignedWord) (padded : Small) (family : (Small × Trace) × ℕ)
    (E : ℕ) (hE : E ≤ 155*family.2) :
    E+(mixWithExtras alpha padded family).2 ≤ 155*(mixWithExtras alpha padded family).1.2 := by
  have ha := BinaryDirectFactoryNormalizationExtras.NestedBinaryAssembly.binary_extra alpha family.1.1 padded
  simp only [mixWithExtras]
  omega

theorem mix_extra (alpha : SignedWord) (padded : Small) (family : (Small × Trace) × ℕ) :
    (mixWithExtras alpha padded family).2 ≤ 155*(mixWithExtras alpha padded family).1.2 := by
  simpa only [Nat.zero_add] using mix_joint alpha padded family 0 (by omega)

theorem profile_extra (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input parameters K bits).2 ≤ 155*(profileWithExtras input parameters K bits).1.2 := by
  let residual := BinaryNestedResidualMeasured.residualWithExtras input parameters
  let padded := BinaryNestedResidualMeasured.pad residual.1.1.1
  let family := BinaryNestedFamilyMeasured.lotteryWithExtras input (parameters.read 2) K bits
  have hr := BinaryDirectFactoryNormalizationExtras.NestedResidual.residual_extra input parameters
  have hf := NestedFamily.lottery_extra input (parameters.read 2) K bits
  have hm := mix_joint (parameters.read 8) padded.1.1 family.1 family.2 hf
  simp only [residual,padded,family] at hm
  simp only [profileWithExtras]
  split_ifs <;> simp only <;> omega

theorem mix_price (alpha : SignedWord) (padded : Small) (family : (Small × Trace) × ℕ) (hA : CanonicalWord alpha)
    (W : ℕ) (hW : 1 ≤ W) (hAlpha : width alpha ≤ W)
    (hFirst : ∀ j,width (family.1.1.weight.read j) ≤ W) (hSecond : ∀ j,width (padded.weight.read j) ≤ W)
    (P U : ℕ) (hFamily : family.2 ≤ P ∧ usage family.1.2 ≤ U) :
    (mixWithExtras alpha padded family).1.2+(mixWithExtras alpha padded family).2 ≤ 156*(P+BinaryNestedBinaryAssemblyMeasured.workEnvelope W+8) ∧
      usage (mixWithExtras alpha padded family).1.1.2 ≤ U+BinaryNestedBinaryAssemblyMeasured.envelope W+64 := by
  have he := mix_extra alpha padded family
  have ho := mix_bounds alpha padded family hA W hW hAlpha hFirst hSecond P U hFamily
  simp only [mixWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem profile_price (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input parameters K bits).1.2+(profileWithExtras input parameters K bits).2 ≤ 156*(workEnvelope s K) ∧ usage (profileWithExtras input parameters K bits).1.1.2 ≤ envelope s K := by
  have he := profile_extra input parameters K bits
  have ho := profile_bounds input parameters hC hParameters s hs hH K bits
  simp only [profileWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedThirdProfile

namespace NestedProfile
open BinaryNestedProfileMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem ordered_extra (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) :
    (orderedWithExtras input parameters regime K bits).2 ≤ 155*(orderedWithExtras input parameters regime K bits).1.2 := by
  have hf := NestedFirstProfile.profile_extra input K bits
  have hs := NestedSecondProfile.profile_extra input parameters K bits
  have ht := NestedThirdProfile.profile_extra input parameters K bits
  simp only [orderedWithExtras,retain]
  split_ifs <;> omega

theorem profile_extra (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input K bits).2 ≤ 155*(profileWithExtras input K bits).1.2 := by
  have hp := NestedControl.run_extra input
  simp only [profileWithExtras]
  split
  · dsimp only; omega
  · rename_i selected h
    have hc := ordered_extra selected.1.1.1 selected.1.2 selected.2 K bits
    simp only [BinaryNestedReferenceMeasured.restore]
    split <;> simp only <;> omega

theorem ordered_price (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (orderedWithExtras input parameters regime K bits).1.2+(orderedWithExtras input parameters regime K bits).2 ≤ 156*(orderedPrice s K) ∧ usage (orderedWithExtras input parameters regime K bits).1.1.2 ≤ orderedEnvelope s K := by
  have he := ordered_extra input parameters regime K bits
  have ho := ordered_bounds input parameters regime hC hParameters s hs hH K bits
  simp only [orderedWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem profile_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input K bits).1.2+(profileWithExtras input K bits).2 ≤ 156*(workEnvelope s K) ∧ usage (profileWithExtras input K bits).1.1.2 ≤ envelope s K := by
  have he := profile_extra input K bits
  have ho := profile_bounds input hC s hs hH K bits
  simp only [profileWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedProfile

end Blotto.BinaryNestedFactoryNormalizationExtras
