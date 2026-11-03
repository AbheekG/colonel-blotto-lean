import Blotto.BinaryFactoryExpressionExtras
import Blotto.BinaryNestedBinaryAssemblyMeasured
import Blotto.BinaryNestedFirstAssemblyMeasured
import Blotto.BinaryNestedOrderMeasured
import Blotto.BinaryNestedResidualMeasured
import Blotto.BinaryNestedSecondUniformMeasured
import Blotto.BinaryReflectedSystemMeasured
import Blotto.BinaryReflectedTerminalInputMeasured
import Blotto.BinarySmallUniformDescriptorMeasured
import Blotto.BinarySmallUniformPreparationMeasured
import Blotto.BinarySmallUniformSplitMeasured

/-! The actual producers retain normalization charges. Their original result,
trace and source-work records are unchanged. All component prices retain every
original premise. Native counter evaluation and root forwarding remain separate. -/
namespace Blotto.BinaryDirectFactoryNormalizationExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] BinaryNormalizedCoordinate.opcode BinaryLifetimeArrayExtras.build
attribute [local irreducible] BinaryNestedBinaryAssemblyMeasured.weightsWithExtras
attribute [local irreducible] BinaryNestedBinaryAssemblyMeasured.fromComplementWithExtras
attribute [local irreducible] BinaryNestedBinaryAssemblyMeasured.binaryWithExtras
attribute [local irreducible] BinaryNestedFirstAssemblyMeasured.rowShiftWithExtras
attribute [local irreducible] BinaryNestedFirstAssemblyMeasured.rowsShiftWithExtras
attribute [local irreducible] BinaryNestedFirstAssemblyMeasured.shiftWithExtras
attribute [local irreducible] BinaryNestedOrderMeasured.orderWithExtras
attribute [local irreducible] BinaryNestedResidualMeasured.environmentWithExtras
attribute [local irreducible] BinaryNestedResidualMeasured.fromEnvironmentWithExtras
attribute [local irreducible] BinaryNestedResidualMeasured.residualWithExtras
attribute [local irreducible] BinaryNestedSecondUniformMeasured.prepareWithExtras
attribute [local irreducible] BinaryReflectedSystemMeasured.fromParametersWithExtras
attribute [local irreducible] BinaryReflectedSystemMeasured.capacityWithExtras
attribute [local irreducible] BinaryReflectedTerminalInputMeasured.terminalWithExtras
attribute [local irreducible] BinarySmallUniformDescriptorMeasured.childWithExtras
attribute [local irreducible] BinarySmallUniformPreparationMeasured.prepareWithExtras
attribute [local irreducible] BinarySmallUniformSplitMeasured.arithmeticWithExtras
attribute [local irreducible] BinarySmallUniformSplitMeasured.splitWithExtras

namespace NestedBinaryAssembly
open BinaryNestedBinaryAssemblyMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage

theorem weights_extra (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) :
    (weightsWithExtras p q first second).2 ≤ 155*(weightsWithExtras p q first second).1.2 := by
  unfold weightsWithExtras
  apply BinaryLifetimeArrayExtras.build_bound 18 _ 155
  intro slot
  refine Fin.addCases (n := 9) (m := 9) (fun j => ?_) (fun j => ?_) slot <;>
    simp only [Fin.addCases_left,Fin.addCases_right]
  · exact BinaryNormalizationExtraWork.opcode_bound .mul p (first.read j)
  · exact BinaryNormalizationExtraWork.opcode_bound .mul q (second.read j)

theorem fromComplement_joint (p : SignedWord) (first second : Small)
    (complement : (SignedWord × Trace) × ℕ) (E : ℕ) (hE : E ≤ 155*complement.2) :
    E+(fromComplementWithExtras p first second complement).2 ≤ 155*(fromComplementWithExtras p first second complement).1.2 := by
  have hw := weights_extra p complement.1.1 first.weight second.weight
  simp only [fromComplementWithExtras,collect]
  omega

theorem fromComplement_extra (p : SignedWord) (first second : Small) (complement : (SignedWord × Trace) × ℕ) :
    (fromComplementWithExtras p first second complement).2 ≤ 155*(fromComplementWithExtras p first second complement).1.2 := by
  simpa only [Nat.zero_add] using fromComplement_joint p first second complement 0 (by omega)

theorem binary_extra (p : SignedWord) (first second : Small) :
    (binaryWithExtras p first second).2 ≤ 155*(binaryWithExtras p first second).1.2 := by
  have h := fromComplement_joint p first second
    (BinaryNormalizedCoordinate.opcode .sub BinaryExpressionCompiler.Constant.one.word p).1
    (BinaryNormalizedCoordinate.opcode .sub BinaryExpressionCompiler.Constant.one.word p).2
    (BinaryNormalizationExtraWork.opcode_bound .sub BinaryExpressionCompiler.Constant.one.word p)
  simpa only [binaryWithExtras] using h

theorem weights_price (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) (W : ℕ)
    (hp : width p ≤ W) (hq : width q ≤ W) (hf : ∀ j,width (first.read j) ≤ W) (hs : ∀ j,width (second.read j) ≤ W) :
    (weightsWithExtras p q first second).1.2+(weightsWithExtras p q first second).2 ≤ 156*(weightPrice W) ∧ usage (weightsWithExtras p q first second).1.1.2 ≤ weightEnvelope W := by
  have he := weights_extra p q first second
  have ho := weights_bounds p q first second W hp hq hf hs
  simp only [weightsWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem fromComplement_price (p : SignedWord) (first second : Small) (complement : (SignedWord × Trace) × ℕ)
    (W : ℕ) (hp : width p ≤ W) (hc : width complement.1.1 ≤ W)
    (hf : ∀ j,width (first.weight.read j) ≤ W) (hs : ∀ j,width (second.weight.read j) ≤ W)
    (C U : ℕ) (hComplement : complement.2 ≤ C ∧ usage complement.1.2 ≤ U) :
    (fromComplementWithExtras p first second complement).1.2+(fromComplementWithExtras p first second complement).2 ≤ 156*(C+weightPrice W+2*23176+16) ∧
    usage (fromComplementWithExtras p first second complement).1.1.2 ≤ U+weightEnvelope W+2*11807+128 := by
  have he := fromComplement_extra p first second complement
  have ho := fromComplement_bounds p first second complement W hp hc hf hs C U hComplement
  simp only [fromComplementWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem binary_price (p : SignedWord) (first second : Small) (hP : CanonicalWord p) (W : ℕ) (hW : 1 ≤ W)
    (hp : width p ≤ W) (hf : ∀ j,width (first.weight.read j) ≤ W) (hs : ∀ j,width (second.weight.read j) ≤ W) :
    (binaryWithExtras p first second).1.2+(binaryWithExtras p first second).2 ≤ 156*(workEnvelope W) ∧ usage (binaryWithExtras p first second).1.1.2 ≤ envelope W := by
  have he := binary_extra p first second
  have ho := binary_bounds p first second hP W hW hp hf hs
  simp only [binaryWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedBinaryAssembly

namespace NestedFirstAssembly
open BinaryNestedFirstAssemblyMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage

theorem rowShift_extra (row : FixedArrayTable 3 SignedWord) (x : SignedWord) :
    (rowShiftWithExtras row x).2 ≤ 155*(rowShiftWithExtras row x).1.2 := by
  have h := BinaryNormalizationExtraWork.opcode_bound .add (row.read 2) x
  simp only [rowShiftWithExtras,rowFrom]
  omega

theorem rowsShift_extra (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) :
    (rowsShiftWithExtras rows x).2 ≤ 155*(rowsShiftWithExtras rows x).1.2 := by
  unfold rowsShiftWithExtras
  exact BinaryLifetimeArrayExtras.build_bound 9 _ 155 (fun slot => rowShift_extra (rows.read slot) x)

theorem shift_extra (table : Segment) (x : SignedWord) :
    (shiftWithExtras table x).2 ≤ 155*(shiftWithExtras table x).1.2 := by
  have hp := rowsShift_extra table.P x
  have hq := rowsShift_extra table.Q x
  simp only [shiftWithExtras]
  omega

theorem rowShift_price (row : FixedArrayTable 3 SignedWord) (x : SignedWord) (W : ℕ)
    (hRow : width (row.read 2) ≤ W) (hX : width x ≤ W) :
    (rowShiftWithExtras row x).1.2+(rowShiftWithExtras row x).2 ≤ 156*(rowPrice W) ∧ usage (rowShiftWithExtras row x).1.1.2 ≤ rowEnvelope W := by
  have he := rowShift_extra row x
  have ho := rowShift_bounds row x W hRow hX
  simp only [rowShiftWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem rowsShift_price (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) (W : ℕ)
    (hRows : ∀ slot,width ((rows.read slot).read 2) ≤ W) (hX : width x ≤ W) :
    (rowsShiftWithExtras rows x).1.2+(rowsShiftWithExtras rows x).2 ≤ 156*(rowsPrice W) ∧ usage (rowsShiftWithExtras rows x).1.1.2 ≤ rowsEnvelope W := by
  have he := rowsShift_extra rows x
  have ho := rowsShift_bounds rows x W hRows hX
  simp only [rowsShiftWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem shift_price (table : Segment) (x : SignedWord) (W : ℕ)
    (hP : ∀ slot,width ((table.P.read slot).read 2) ≤ W)
    (hQ : ∀ slot,width ((table.Q.read slot).read 2) ≤ W) (hX : width x ≤ W) :
    (shiftWithExtras table x).1.2+(shiftWithExtras table x).2 ≤ 156*(shiftPrice W) ∧ usage (shiftWithExtras table x).1.1.2 ≤ shiftEnvelope W := by
  have he := shift_extra table x
  have ho := shift_bounds table x W hP hQ hX
  simp only [shiftWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedFirstAssembly

namespace NestedOrder
open BinaryNestedOrderMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem order_extra (input : Input) :
    (orderWithExtras input).2 ≤ 155*(orderWithExtras input).1.2 := by
  have hl := BinaryNormalizationExtraWork.opcode_bound .minimum input.a input.d
  have hh := BinaryNormalizationExtraWork.opcode_bound .maximum input.a input.d
  simp only [orderWithExtras,collect]
  omega

theorem order_price (input : Input) (hC : input.Canonical) (s : ℕ)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (orderWithExtras input).1.2+(orderWithExtras input).2 ≤ 156*(workEnvelope s) ∧ usage (orderWithExtras input).1.1.2 ≤ BinaryNestedOrderLifetime.orderEnvelope s := by
  have he := order_extra input
  have ho := order_bounds input hC s hH
  simp only [orderWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedOrder

namespace NestedResidual
open BinaryNestedResidualMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage

theorem environment_extra (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    (environmentWithExtras input parameters).2 ≤ 155*(environmentWithExtras input parameters).1.2 := by
  have h := BinaryNormalizationExtraWork.opcode_bound .sub input.M input.c
  simp only [environmentWithExtras,environmentFrom]
  omega

theorem fromEnvironment_joint (env : (FixedArrayTable 5 SignedWord × Trace) × ℕ)
    (E : ℕ) (hE : E ≤ 155*env.2) :
    E+(fromEnvironmentWithExtras env).2 ≤ 155*(fromEnvironmentWithExtras env).1.2 := by
  have ht := BinaryFactoryExpressionExtras.Residual.descriptor_extra env.1.1
  simp only [fromEnvironmentWithExtras]
  omega

theorem fromEnvironment_extra (env : (FixedArrayTable 5 SignedWord × Trace) × ℕ) :
    (fromEnvironmentWithExtras env).2 ≤ 155*(fromEnvironmentWithExtras env).1.2 := by
  simpa only [Nat.zero_add] using fromEnvironment_joint env 0 (by omega)

theorem residual_extra (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    (residualWithExtras input parameters).2 ≤ 155*(residualWithExtras input parameters).1.2 := by
  have h := fromEnvironment_joint (environmentWithExtras input parameters).1
    (environmentWithExtras input parameters).2 (environment_extra input parameters)
  simpa only [residualWithExtras] using h

theorem environment_price (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (s : ℕ) (hH : BinaryNestedParameterWork.InputHeight input s) :
    (environmentWithExtras input parameters).1.2+(environmentWithExtras input parameters).2 ≤ 156*(environmentPrice s) ∧ usage (environmentWithExtras input parameters).1.1.2 ≤ environmentEnvelope s := by
  have he := environment_extra input parameters
  have ho := environment_bounds input parameters hC s hH
  simp only [environmentWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem fromEnvironment_price (env : (FixedArrayTable 5 SignedWord × Trace) × ℕ) (hC : ∀ j,CanonicalWord (env.1.1.read j))
    (H : ℕ) (hs : 3 ≤ H) (hHeight : BinarySyntaxUniformWork.EnvHeight env.1.1 H)
    (P U : ℕ) (hEnv : env.2 ≤ P ∧ usage env.1.2 ≤ U) :
    (fromEnvironmentWithExtras env).1.2+(fromEnvironmentWithExtras env).2 ≤ 156*(P+BinaryNestedResidualDescriptorMeasured.workEnvelope H+8) ∧
      usage (fromEnvironmentWithExtras env).1.1.2 ≤ U+BinaryNestedResidualDescriptorMeasured.envelope H+64 := by
  have he := fromEnvironment_extra env
  have ho := fromEnvironment_bounds env hC H hs hHeight P U hEnv
  simp only [fromEnvironmentWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem residual_price (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    (residualWithExtras input parameters).1.2+(residualWithExtras input parameters).2 ≤ 156*(workEnvelope s) ∧ usage (residualWithExtras input parameters).1.1.2 ≤ envelope s := by
  have he := residual_extra input parameters
  have ho := residual_bounds input parameters hC hParameters s hs hH
  simp only [residualWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedResidual

namespace NestedSecondUniform
open BinaryNestedSecondUniformMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage

theorem prepare_extra (input : Input) (mirror : SignedWord) :
    (prepareWithExtras input mirror).2 ≤ 155*(prepareWithExtras input mirror).1.2 := by
  have hb := BinaryNormalizationExtraWork.opcode_bound .sub input.M mirror
  have hl := BinaryNormalizationExtraWork.opcode_bound .sub input.t mirror
  simp only [prepareWithExtras,collectInput]
  omega

theorem prepare_price (input : Input) (mirror : SignedWord) (hC : input.Canonical) (hM : CanonicalWord mirror)
    (s : ℕ) (hH : BinaryNestedParameterWork.InputHeight input s) (hMH : RationalHeight (value mirror) s) :
    (prepareWithExtras input mirror).1.2+(prepareWithExtras input mirror).2 ≤ 156*(inputPrice s) ∧ usage (prepareWithExtras input mirror).1.1.2 ≤ inputEnvelope s := by
  have he := prepare_extra input mirror
  have ho := prepare_bounds input mirror hC hM s hH hMH
  simp only [prepareWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedSecondUniform

namespace ReflectedSystem
open BinaryReflectedSystemMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryReflectedFourSetup BinaryPRGHeapTraceUsage BinaryLifetimeUsage

theorem fromParameters_extra (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) :
    (fromParametersWithExtras input parameters).2 ≤ 155*(fromParametersWithExtras input parameters).1.2 := by
  have hs := BinaryNormalizationExtraWork.opcode_bound .mul (parameters.read 6) (parameters.read 5)
  have ht := BinaryLifetimeArrayExtras.build_bound 3 (fun j => BinaryNormalizedCoordinate.opcode .mul (parameters.read 4) ((lengths input).1.1.read j)) 155 (fun j => BinaryNormalizationExtraWork.opcode_bound .mul _ _)
  have hi := BinaryLifetimeArrayExtras.build_bound 3 (fun j => BinaryNormalizedCoordinate.opcode .mul (BinaryNormalizedCoordinate.opcode .mul (parameters.read 6) (parameters.read 5)).1.1.1 ((lengths input).1.1.read j)) 155 (fun j => BinaryNormalizationExtraWork.opcode_bound .mul _ _)
  simp only [fromParametersWithExtras,assemble]
  omega

theorem capacity_extra (system : System) :
    (capacityWithExtras system).2 ≤ 155*(capacityWithExtras system).1.2 := by
  unfold capacityWithExtras
  exact BinaryLifetimeArrayExtras.build_bound 3 _ 155 (fun j => BinaryNormalizationExtraWork.opcode_bound .sub _ _)

theorem fromParameters_price (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord)
    (hC : input.Canonical) (hP : ∀ j,CanonicalWord (parameters.read j)) (t : ℕ)
    (hParameters : ∀ j,RationalHeight (value (parameters.read j)) t)
    (hLengths : ∀ j,RationalHeight (value ((originalLengths input).read j)) t) :
    (fromParametersWithExtras input parameters).1.2+(fromParametersWithExtras input parameters).2 ≤ 156*(workEnvelope t) ∧ usage (fromParametersWithExtras input parameters).1.1.2 ≤ envelope t := by
  have he := fromParameters_extra input parameters
  have ho := fromParameters_bounds input parameters hC hP t hParameters hLengths
  simp only [fromParametersWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem capacity_price (system : System) (hC : system.Canonical) (t : ℕ)
    (hLong : ∀ j,RationalHeight (value (system.long.read j)) t)
    (hShort : ∀ j,RationalHeight (value (system.short.read j)) t) :
    (capacityWithExtras system).1.2+(capacityWithExtras system).2 ≤ 156*(capacityPrice t) ∧ usage (capacityWithExtras system).1.1.2 ≤ capacityEnvelope t := by
  have he := capacity_extra system
  have ho := capacity_bounds system hC t hLong hShort
  simp only [capacityWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end ReflectedSystem

namespace ReflectedTerminalInput
open BinaryReflectedTerminalInputMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

theorem terminal_extra {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) :
    (terminalWithExtras prepared state).2 ≤ 155*(terminalWithExtras prepared state).1.2 := by
  have h := BinaryNormalizationExtraWork.opcode_bound .div
    (state.resource.read (BinaryReflectedFocusMeasured.preparedFocus prepared state).1.1)
    (prepared.capacity.read (BinaryReflectedFocusMeasured.preparedFocus prepared state).1.1)
  simp only [terminalWithExtras,collect]
  omega

theorem terminal_price {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) (W : ℕ) (hW : 1 ≤ W)
    (hCap : ∀ j,width (prepared.capacity.read j) ≤ W) (hResource : ∀ j,width (state.resource.read j) ≤ W) :
    (terminalWithExtras prepared state).1.2+(terminalWithExtras prepared state).2 ≤ 156*(terminalPrice W) := by
  have he := terminal_extra prepared state
  have ho := terminal_work prepared state W hW hCap hResource
  simp only [terminalWithExtras_compat] at he ⊢
  omega

end ReflectedTerminalInput

namespace SmallUniformDescriptor
open BinarySmallUniformDescriptorMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight BinaryLifetimeUsage

theorem child_extra (input : BinarySmallUniformCompiler.Input) :
    (childWithExtras input).2 ≤ 155*(childWithExtras input).1.2 := by
  have h := BinaryNormalizationExtraWork.opcode_bound .add input.l0 input.l1
  simp only [childWithExtras]
  omega

theorem child_price (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hH : BinarySmallUniformFactoryWork.InputHeight input s) :
    (childWithExtras input).1.2+(childWithExtras input).2 ≤ 156*(childPrice s) ∧ usage (childWithExtras input).1.1.2 ≤ childEnvelope s := by
  have he := child_extra input
  have ho := child_bounds input hC s hH
  simp only [childWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end SmallUniformDescriptor

namespace SmallUniformPreparation
open BinarySmallUniformPreparationMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight BinaryLifetimeUsage

theorem prepare_extra (input : BinaryFourParameters.Input) :
    (prepareWithExtras input).2 ≤ 155*(prepareWithExtras input).1.2 := by
  have hp := BinaryFactoryExpressionExtras.FourParameters.prepare_extra input
  have hf := BinaryNormalizationExtraWork.opcode_bound .mul ((BinaryFourParametersMeasured.prepareWithExtras input).1.1.1.read 5) input.u
  have hs := BinaryNormalizationExtraWork.opcode_bound .mul ((BinaryFourParametersMeasured.prepareWithExtras input).1.1.1.read 5) input.v
  have ht := BinaryNormalizationExtraWork.opcode_bound .mul ((BinaryFourParametersMeasured.prepareWithExtras input).1.1.1.read 5) input.w
  simp only [prepareWithExtras,collect]
  omega

theorem prepare_price (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (prepareWithExtras input).1.2+(prepareWithExtras input).2 ≤ 156*(workEnvelope s) ∧ usage (prepareWithExtras input).1.1.2 ≤ envelope s := by
  have he := prepare_extra input
  have ho := prepare_bounds input source hC hR s hs hH
  simp only [prepareWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end SmallUniformPreparation

namespace SmallUniformSplit
open BinarySmallUniformSplitMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight

theorem arithmetic_extra (first second coordinate : SignedWord) :
    (arithmeticWithExtras first second coordinate).2 ≤ 155*(arithmeticWithExtras first second coordinate).1.2 := by
  let total := BinaryNormalizedCoordinate.opcode .add first second
  let low := BinaryNormalizedCoordinate.opcode .div first total.1.1.1
  let high := BinaryNormalizedCoordinate.opcode .div second total.1.1.1
  have ht := BinaryNormalizationExtraWork.opcode_bound .add first second
  have hl := BinaryNormalizationExtraWork.opcode_bound .div first total.1.1.1
  have hh := BinaryNormalizationExtraWork.opcode_bound .div second total.1.1.1
  have hp := BinaryNormalizationExtraWork.opcode_bound .mul low.1.1.1 coordinate
  have hq := BinaryNormalizationExtraWork.opcode_bound .mul high.1.1.1 coordinate
  simp only [arithmeticWithExtras,joinArithmetic]
  simp only [total,low,high] at hl hh hp hq
  omega

theorem split_extra (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    (splitWithExtras first second row).2 ≤ 155*(splitWithExtras first second row).1.2 := by
  have h := arithmetic_extra first second (row.read 0)
  simp only [splitWithExtras,collect]
  omega

theorem arithmetic_price (first second coordinate : SignedWord)
    (hFirstC : CanonicalWord first) (hSecondC : CanonicalWord second) (hCoordinateC : CanonicalWord coordinate)
    (s : ℕ) (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s)
    (hCoordinate : RationalHeight (value coordinate) s) :
    (arithmeticWithExtras first second coordinate).1.2+(arithmeticWithExtras first second coordinate).2 ≤ 156*(5*opcodePrice (expressionHeightBudget s 2)+16) := by
  have he := arithmetic_extra first second coordinate
  have ho := arithmetic_work first second coordinate hFirstC hSecondC hCoordinateC s hFirst hSecond hCoordinate
  simp only [arithmeticWithExtras_compat] at he ⊢
  omega

theorem split_price (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hFirstC : CanonicalWord first) (hSecondC : CanonicalWord second)
    (hRowC : ∀ j,CanonicalWord (row.read j)) (s : ℕ)
    (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s)
    (hRow : ∀ j,RationalHeight (value (row.read j)) s) :
    (splitWithExtras first second row).1.2+(splitWithExtras first second row).2 ≤ 156*(workEnvelope s) ∧ usage (splitWithExtras first second row).1.1.2 ≤ envelope s := by
  have he := split_extra first second row
  have ho := split_bounds first second row hFirstC hSecondC hRowC s hFirst hSecond hRow
  simp only [splitWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end SmallUniformSplit

end Blotto.BinaryDirectFactoryNormalizationExtras
