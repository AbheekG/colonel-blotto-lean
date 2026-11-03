import Blotto.BinaryDirectFactoryNormalizationExtras
import Blotto.BinaryThreeFactoryMeasured
import Blotto.BinarySmallUniformDescriptorMeasured
import Blotto.BinarySmallUniformFactoryMeasured
import Blotto.BinaryFourGluingParentsMeasured
import Blotto.BinaryFourGluingMeasured
import Blotto.BinaryNestedSecondUniformMeasured
import Blotto.BinaryReflectedPreparationMeasured

/-! Actual higher factories retain only reached normalization fields, without
replaying children. Old result/trace/source records and all original component
price premises remain exact. Complete root/native/physical joins are separate. -/
namespace Blotto.BinaryHigherFactoryNormalizationExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] BinaryLifetimeArrayExtras.build BinaryThreeFactoryMeasured.orderedWithExtras BinaryThreeFactoryMeasured.descriptorWithExtras BinarySmallUniformDescriptorMeasured.descriptorWithExtras BinarySmallUniformFactoryMeasured.descriptorWithExtras BinaryFourGluingParentsMeasured.runWithExtras BinaryFourGluingMeasured.descriptorWithExtras BinaryNestedSecondUniformMeasured.fromPreparedWithExtras BinaryNestedSecondUniformMeasured.uniformWithExtras BinaryReflectedPreparationMeasured.fromSystemWithExtras BinaryReflectedPreparationMeasured.fromParametersWithExtras BinaryReflectedPreparationMeasured.prepareWithExtras BinaryNestedBinaryAssemblyMeasured.weightsWithExtras BinaryNestedBinaryAssemblyMeasured.fromComplementWithExtras BinaryNestedBinaryAssemblyMeasured.binaryWithExtras BinaryNestedFirstAssemblyMeasured.rowShiftWithExtras BinaryNestedFirstAssemblyMeasured.rowsShiftWithExtras BinaryNestedFirstAssemblyMeasured.shiftWithExtras BinaryNestedOrderMeasured.orderWithExtras BinaryNestedResidualMeasured.environmentWithExtras BinaryNestedResidualMeasured.fromEnvironmentWithExtras BinaryNestedResidualMeasured.residualWithExtras BinaryNestedSecondUniformMeasured.prepareWithExtras BinaryReflectedSystemMeasured.fromParametersWithExtras BinaryReflectedSystemMeasured.capacityWithExtras BinaryReflectedTerminalInputMeasured.terminalWithExtras BinarySmallUniformDescriptorMeasured.childWithExtras BinarySmallUniformPreparationMeasured.prepareWithExtras BinarySmallUniformSplitMeasured.arithmeticWithExtras BinarySmallUniformSplitMeasured.splitWithExtras BinaryQuadraticThreeFactoryMeasured.vertexRowWithExtras BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras BinaryThreeGeometryMeasured.geometryWithExtras BinaryThreeGeometryMeasured.regimeWithExtras BinaryOverlapGluingMeasured.fromEnvironmentWithExtras BinaryOverlapGluingMeasured.slotWithExtras BinaryFourParametersMeasured.prepareWithExtras BinaryNestedParameterMeasured.runProgramsWithExtras BinaryNestedParameterMeasured.prepareAtWithExtras BinaryNestedParameterMeasured.prepareWithExtras BinaryNestedParameterMeasured.geometryWithExtras BinaryNestedResidualDescriptorMeasured.weightsWithExtras BinaryNestedResidualDescriptorMeasured.vertexRowWithExtras BinaryNestedResidualDescriptorMeasured.rowsWithExtras BinaryNestedResidualDescriptorMeasured.descriptorWithExtras BinaryOverlapGluingMeasured.descriptorWithExtras

namespace ThreeFactory
open BinaryThreeFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryThreeInputCompiler BinarySyntaxUniformWork

theorem ordered_extra (input : Input) :
    (orderedWithExtras input).2 ≤ 155*(orderedWithExtras input).1.2 := by
  let env := BinaryThreeGeometryMeasured.environment input
  have hr := BinaryFactoryExpressionExtras.ThreeGeometry.regime_extra env.1.1
  have hg := BinaryFactoryExpressionExtras.ThreeGeometry.geometry_extra env.1.1
  have hf := BinaryFactoryExpressionExtras.ThreeFactory.descriptor_extra (BinaryThreeGeometryMeasured.geometryWithExtras env.1.1).1.1.1
  simp only [env] at hr hg hf
  simp only [orderedWithExtras]
  split_ifs <;> dsimp only <;> omega

theorem descriptor_extra (input : Input) :
    (descriptorWithExtras input).2 ≤ 155*(descriptorWithExtras input).1.2 := by
  have h := ordered_extra (if (BinaryQuadraticExpressionMeasured.compare input.a input.d).1.1 then input else ⟨input.B,input.d,input.a,input.c,input.p⟩)
  simp only [descriptorWithExtras,restore]
  split_ifs at h ⊢ <;> omega

theorem ordered_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) : (orderedWithExtras input).1.2+(orderedWithExtras input).2 ≤ 156*(orderedWork s) := by
  have he := ordered_extra input
  have ho := ordered_work input hC s hs hH
  simp only [orderedWithExtras_compat] at he ⊢
  omega

theorem descriptor_price (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    (descriptorWithExtras input).1.2+(descriptorWithExtras input).2 ≤ 156*(workEnvelope s) ∧ usage (descriptorWithExtras input).1.1.2 ≤ envelope s := by
  have he := descriptor_extra input
  have ho := descriptor_bounds input hC s hs hH
  simp only [descriptorWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end ThreeFactory

namespace SmallUniformDescriptor
open BinarySmallUniformDescriptorMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight BinaryLifetimeUsage

theorem descriptor_extra (input : BinarySmallUniformCompiler.Input) :
    (descriptorWithExtras input).2 ≤ 155*(descriptorWithExtras input).1.2 := by
  let merged := childWithExtras input
  let table := BinaryThreeFactoryMeasured.descriptorWithExtras merged.1.1.1
  have hm := BinaryDirectFactoryNormalizationExtras.SmallUniformDescriptor.child_extra input
  have ht := ThreeFactory.descriptor_extra merged.1.1.1
  have hp := BinaryLifetimeArrayExtras.build_bound 9 (fun slot => BinarySmallUniformSplitMeasured.splitWithExtras input.l0 input.l1 (table.1.1.1.P.read slot)) 155 (fun slot => BinaryDirectFactoryNormalizationExtras.SmallUniformSplit.split_extra _ _ _)
  have hq := BinaryLifetimeArrayExtras.build_bound 9 (fun slot => BinarySmallUniformSplitMeasured.splitWithExtras input.l0 input.l1 (table.1.1.1.Q.read slot)) 155 (fun slot => BinaryDirectFactoryNormalizationExtras.SmallUniformSplit.split_extra _ _ _)
  simp only [descriptorWithExtras,assemble]
  simp only [merged,table] at ht hp hq
  omega

theorem descriptor_price (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySmallUniformFactoryWork.InputHeight input s) :
    (descriptorWithExtras input).1.2+(descriptorWithExtras input).2 ≤ 156*(workEnvelope s) ∧ usage (descriptorWithExtras input).1.1.2 ≤ envelope s := by
  have he := descriptor_extra input
  have ho := descriptor_bounds input hC s hs hH
  simp only [descriptorWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end SmallUniformDescriptor

namespace SmallUniformFactory
open BinarySmallUniformFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem descriptor_extra (input : BinaryFourParameters.Input) :
    (descriptorWithExtras input).2 ≤ 155*(descriptorWithExtras input).1.2 := by
  have hp := BinaryDirectFactoryNormalizationExtras.SmallUniformPreparation.prepare_extra input
  have ht := SmallUniformDescriptor.descriptor_extra (BinarySmallUniformPreparationMeasured.prepareWithExtras input).1.1.1
  simp only [descriptorWithExtras,collect]
  omega

theorem descriptor_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    (descriptorWithExtras input).1.2+(descriptorWithExtras input).2 ≤ 156*(workEnvelope s) ∧ usage (descriptorWithExtras input).1.1.2 ≤ envelope s := by
  have he := descriptor_extra input
  have ho := descriptor_bounds input source hC hR hCase s hs hH
  simp only [descriptorWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end SmallUniformFactory

namespace FourGluingParents
open BinaryFourGluingParentsMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryFourParentCompiler

theorem run_extra (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (runWithExtras input hC).2 ≤ 155*(runWithExtras input hC).1.2 := by
  let parameters := BinaryFourParametersMeasured.prepareWithExtras input
  have hp := BinaryFactoryExpressionExtras.FourParameters.prepare_extra input
  have hf := ThreeFactory.descriptor_extra (firstInput input parameters.1.1.1)
  have hs := ThreeFactory.descriptor_extra (secondInput input parameters.1.1.1)
  simp only [runWithExtras]
  simp only [parameters] at hf hs
  omega

theorem run_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : (1-source.p)*source.ell ≤ source.w)
    (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    (runWithExtras input hC).1.2+(runWithExtras input hC).2 ≤ 156*(workEnvelope s) ∧ usage (runWithExtras input hC).1.1.2 ≤ envelope s := by
  have he := run_extra input hC
  have ho := run_bounds input source hC hR hCase s hs hH
  simp only [runWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end FourGluingParents

namespace FourGluing
open BinaryFourGluingMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFourParentCompiler

theorem descriptor_extra (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (descriptorWithExtras input hC).2 ≤ 155*(descriptorWithExtras input hC).1.2 := by
  let parents := BinaryFourGluingParentsMeasured.runWithExtras input hC
  have hp := FourGluingParents.run_extra input hC
  have hc := BinaryFactoryExpressionExtras.Gluing.descriptor_extra parents.1.1.1.2.1 parents.1.1.1.2.2 (parents.1.1.1.1.read 1) input.B
  simp only [descriptorWithExtras,collect]
  simp only [parents] at hc
  omega

theorem descriptor_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    (descriptorWithExtras input hC).1.2+(descriptorWithExtras input hC).2 ≤ 156*(workEnvelope s) ∧ usage (descriptorWithExtras input hC).1.1.2 ≤ envelope s := by
  have he := descriptor_extra input hC
  have ho := descriptor_bounds input source hC hR hCase s hs hH
  simp only [descriptorWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end FourGluing

namespace NestedSecondUniform
open BinaryNestedSecondUniformMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage

theorem fromPrepared_joint (prepared : (BinaryNestedSecondUniformMeasured.ThreeInput × Trace) × ℕ) (mirror : SignedWord)
    (E : ℕ) (hE : E ≤ 155*prepared.2) :
    E+(fromPreparedWithExtras prepared mirror).2 ≤ 155*(fromPreparedWithExtras prepared mirror).1.2 := by
  have hc := ThreeFactory.ordered_extra prepared.1.1
  have hs := BinaryDirectFactoryNormalizationExtras.NestedFirstAssembly.shift_extra (BinaryThreeFactoryMeasured.orderedWithExtras prepared.1.1).1.1.1 mirror
  simp only [fromPreparedWithExtras,collect]
  omega

theorem fromPrepared_extra (prepared : (BinaryNestedSecondUniformMeasured.ThreeInput × Trace) × ℕ) (mirror : SignedWord) :
    (fromPreparedWithExtras prepared mirror).2 ≤ 155*(fromPreparedWithExtras prepared mirror).1.2 := by
  simpa only [Nat.zero_add] using fromPrepared_joint prepared mirror 0 (by omega)

theorem uniform_extra (input : Input) (mirror : SignedWord) :
    (uniformWithExtras input mirror).2 ≤ 155*(uniformWithExtras input mirror).1.2 := by
  have h := fromPrepared_joint (prepareWithExtras input mirror).1 mirror (prepareWithExtras input mirror).2
    (BinaryDirectFactoryNormalizationExtras.NestedSecondUniform.prepare_extra input mirror)
  simpa only [uniformWithExtras] using h

theorem fromPrepared_price (prepared : (BinaryNestedSecondUniformMeasured.ThreeInput × Trace) × ℕ) (mirror : SignedWord)
    (hC : prepared.1.1.Canonical) (H : ℕ) (hH : 3 ≤ H)
    (hHeight : BinaryOrderedThreeFactoryWork.InputHeight prepared.1.1 H) (hMirror : width mirror ≤ shiftWidth H)
    (P U : ℕ) (hPrepared : prepared.2 ≤ P ∧ usage prepared.1.2 ≤ U) :
    (fromPreparedWithExtras prepared mirror).1.2+(fromPreparedWithExtras prepared mirror).2 ≤ 156*(P+BinaryThreeFactoryMeasured.orderedWork H+BinaryNestedFirstAssemblyMeasured.shiftPrice (shiftWidth H)+12) ∧
    usage (fromPreparedWithExtras prepared mirror).1.1.2 ≤ U+BinaryThreeFactoryMeasured.orderedEnvelope H+BinaryNestedFirstAssemblyMeasured.shiftEnvelope (shiftWidth H)+64 := by
  have he := fromPrepared_extra prepared mirror
  have ho := fromPrepared_bounds prepared mirror hC H hH hHeight hMirror P U hPrepared
  simp only [fromPreparedWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem uniform_price (input : Input) (mirror : SignedWord) (hC : input.Canonical) (hM : CanonicalWord mirror)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hMH : RationalHeight (value mirror) s) :
    (uniformWithExtras input mirror).1.2+(uniformWithExtras input mirror).2 ≤ 156*(workEnvelope s) ∧ usage (uniformWithExtras input mirror).1.1.2 ≤ envelope s := by
  have he := uniform_extra input mirror
  have ho := uniform_bounds input mirror hC hM s hs hH hMH
  simp only [uniformWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedSecondUniform

namespace ReflectedPreparation
open BinaryReflectedPreparationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryPRGHeapTraceUsage BinaryReflectedPreparationLifetime

theorem fromSystem_extra (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input) :
    (fromSystemWithExtras input hC parameters system hParameters hSystem).2 ≤ 155*(fromSystemWithExtras input hC parameters system hParameters hSystem).1.2 := by
  have hc := BinaryDirectFactoryNormalizationExtras.ReflectedSystem.capacity_extra system.1.1
  simp only [fromSystemWithExtras,assemble]
  omega

theorem fromParameters_joint (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (E : ℕ) (hE : E ≤ 155*parameters.2) :
    E+(fromParametersWithExtras input hC parameters hParameters).2 ≤ 155*(fromParametersWithExtras input hC parameters hParameters).1.2 := by
  have hs := BinaryDirectFactoryNormalizationExtras.ReflectedSystem.fromParameters_extra input parameters.1.1
  have hc := BinaryDirectFactoryNormalizationExtras.ReflectedSystem.capacity_extra (BinaryReflectedSystemMeasured.fromParametersWithExtras input parameters.1.1).1.1.1
  simp only [fromParametersWithExtras,fromSystemWithExtras,assemble]
  omega

theorem fromParameters_extra (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input) :
    (fromParametersWithExtras input hC parameters hParameters).2 ≤ 155*(fromParametersWithExtras input hC parameters hParameters).1.2 := by
  simpa only [Nat.zero_add] using fromParameters_joint input hC parameters hParameters 0 (by omega)

theorem prepare_extra (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (prepareWithExtras input hC).2 ≤ 155*(prepareWithExtras input hC).1.2 := by
  have h := fromParameters_joint input hC (BinaryFourParametersMeasured.prepareWithExtras input).1
    (by simpa only [BinaryFourParametersMeasured.prepareWithExtras_compat] using
      (BinaryFourParametersMeasured.prepare_data input).trans (BinaryReflectedParameterLifetime.prepareWithTrace_erasure input hC))
    (BinaryFourParametersMeasured.prepareWithExtras input).2 (BinaryFactoryExpressionExtras.FourParameters.prepare_extra input)
  simpa only [prepareWithExtras] using h

theorem fromSystem_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ) (system : (System × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hSystem : system.1.1 = BinaryReflectedFourSetup.prepare input)
    (hP : parameters.2 ≤ BinaryFourParametersMeasured.workEnvelope s ∧ usage parameters.1.2 ≤ BinaryFourParametersMeasured.envelope s)
    (hS : system.2 ≤ BinaryReflectedSystemMeasured.workEnvelope (expressionHeightBudget s 12) ∧
      usage system.1.2 ≤ BinaryReflectedSystemMeasured.envelope (expressionHeightBudget s 12)) :
    (fromSystemWithExtras input hC parameters system hParameters hSystem).1.2+(fromSystemWithExtras input hC parameters system hParameters hSystem).2 ≤ 156*(workEnvelope s) ∧
      usage (fromSystemWithExtras input hC parameters system hParameters hSystem).1.1.2 ≤ BinaryReflectedPreparationMeasured.envelope s := by
  have he := fromSystem_extra input hC parameters system hParameters hSystem
  have ho := fromSystem_bounds input source hC hR hCase s hs hH parameters system hParameters hSystem hP hS
  simp only [fromSystemWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem fromParameters_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (parameters : (FixedArrayTable 8 SignedWord × Trace) × ℕ)
    (hParameters : parameters.1.1 = BinaryFourParameters.prepare input)
    (hP : parameters.2 ≤ BinaryFourParametersMeasured.workEnvelope s ∧ usage parameters.1.2 ≤ BinaryFourParametersMeasured.envelope s) :
    (fromParametersWithExtras input hC parameters hParameters).1.2+(fromParametersWithExtras input hC parameters hParameters).2 ≤ 156*(workEnvelope s) ∧
      usage (fromParametersWithExtras input hC parameters hParameters).1.1.2 ≤ BinaryReflectedPreparationMeasured.envelope s := by
  have he := fromParameters_extra input hC parameters hParameters
  have ho := fromParameters_bounds input source hC hR hCase s hs hH parameters hParameters hP
  simp only [fromParametersWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem prepare_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (prepareWithExtras input hC).1.2+(prepareWithExtras input hC).2 ≤ 156*(workEnvelope s) ∧ usage (prepareWithExtras input hC).1.1.2 ≤ BinaryReflectedPreparationMeasured.envelope s := by
  have he := prepare_extra input hC
  have ho := prepare_bounds input source hC hR hCase s hs hH
  simp only [prepareWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end ReflectedPreparation

end Blotto.BinaryHigherFactoryNormalizationExtras
