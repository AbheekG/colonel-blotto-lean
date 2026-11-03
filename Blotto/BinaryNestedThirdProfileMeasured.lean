import Blotto.BinaryNestedResidualMeasured
import Blotto.BinaryNestedSecondProfileMeasured
import Blotto.BinaryNestedThirdProfileLifetime

/-! The third profile consumes the actual measured residual and its nine-slot
padding, then only the reached measured family mixture or eighteen-slot pad.
The supplied parameter table is shared; original fields derive all prices. -/
namespace Blotto.BinaryNestedThirdProfileMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1500000

abbrev Input := BinaryNestedParameters.Input
abbrev Residual := BinaryStoredOverlapEnvironment.Segment 3 3
abbrev Small := BinaryStoredOverlapEnvironment.Segment 3 9
abbrev Large := BinaryStoredOverlapEnvironment.Segment 3 18

set_option cleanup.letToHave false in
def mixWithExtras (alpha : SignedWord) (padded : Small) (family : (Small × Trace) × ℕ) : ((Large × Trace) × ℕ) × ℕ :=
  let assembled := BinaryNestedBinaryAssemblyMeasured.binaryWithExtras alpha family.1.1 padded
  (((assembled.1.1.1,wrap 32 2 [family.1.2,assembled.1.1.2]),family.2+assembled.1.2+8),assembled.2)

def mix (alpha : SignedWord) (padded : Small) (family : (Small × Trace) × ℕ) : (Large × Trace) × ℕ :=
  (mixWithExtras alpha padded family).1

theorem mixWithExtras_compat (alpha : SignedWord) (padded : Small) (family : (Small × Trace) × ℕ) :
    (mixWithExtras alpha padded family).1 = mix alpha padded family := rfl

theorem mix_record (alpha : SignedWord) (padded : Small) (family : (Small × Trace) × ℕ) :
    mix alpha padded family =
  let assembled := BinaryNestedBinaryAssemblyMeasured.binary alpha family.1.1 padded
  ((assembled.1.1,wrap 32 2 [family.1.2,assembled.1.2]),family.2+assembled.2+8) := by
  simp only [mix,mixWithExtras,BinaryNestedBinaryAssemblyMeasured.weightsWithExtras_compat,BinaryNestedBinaryAssemblyMeasured.fromComplementWithExtras_compat,BinaryNestedBinaryAssemblyMeasured.binaryWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,BinaryNestedResidualMeasured.environmentWithExtras_compat,BinaryNestedResidualMeasured.fromEnvironmentWithExtras_compat,BinaryNestedResidualMeasured.residualWithExtras_compat,BinaryNestedFamilyMeasured.prepareWithExtras_compat,BinaryNestedFamilyMeasured.fromFamilyWithExtras_compat,BinaryNestedFamilyMeasured.lotteryWithExtras_compat,BinaryNestedSecondProfileMeasured.mixWithExtras_compat,BinaryNestedSecondProfileMeasured.profileWithExtras_compat]
  try { split_ifs <;> rfl }

def finish (residual : (Residual × Trace) × ℕ) (padded : (Small × Trace) × ℕ) (guard : (Bool × Trace) × ℕ)
    (regular : Unit → (Large × Trace) × ℕ) : (Large × Trace) × ℕ :=
  let chosen := if !guard.1.1 then regular () else BinaryNestedReferenceMeasured.pad padded.1.1
  ((chosen.1.1,wrap 40 3 [residual.1.2,padded.1.2,guard.1.2,chosen.1.2]),residual.2+padded.2+guard.2+chosen.2+16)

set_option cleanup.letToHave false in
def profileWithExtras (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : ((Large × Trace) × ℕ) × ℕ :=
  let residual := BinaryNestedResidualMeasured.residualWithExtras input parameters
  let padded := BinaryNestedResidualMeasured.pad residual.1.1.1
  let guard := BinaryQuadraticExpressionMeasured.compare (parameters.read 2) BinaryRationalOpcode.zero
  let chosen := if !guard.1.1 then
      let family := BinaryNestedFamilyMeasured.lotteryWithExtras input (parameters.read 2) K bits
      let assembled := mixWithExtras (parameters.read 8) padded.1.1 family.1
      (assembled.1,family.2+assembled.2)
    else (BinaryNestedReferenceMeasured.pad padded.1.1,0)
  (((chosen.1.1.1,wrap 40 3 [residual.1.1.2,padded.1.2,guard.1.2,chosen.1.1.2]),residual.1.2+padded.2+guard.2+chosen.1.2+16),residual.2+chosen.2)

def profile (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : (Large × Trace) × ℕ :=
  (profileWithExtras input parameters K bits).1

theorem profileWithExtras_compat (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input parameters K bits).1 = profile input parameters K bits := rfl

attribute [local irreducible] BinaryNestedFamilyMeasured.lotteryWithExtras BinaryNestedResidualMeasured.residualWithExtras mixWithExtras

theorem profile_record (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    profile input parameters K bits =
  let residual := BinaryNestedResidualMeasured.residual input parameters
  let padded := BinaryNestedResidualMeasured.pad residual.1.1
  let guard := BinaryQuadraticExpressionMeasured.compare (parameters.read 2) BinaryRationalOpcode.zero
  finish residual padded guard (fun _ => mix (parameters.read 8) padded.1.1 (BinaryNestedFamilyMeasured.lottery input (parameters.read 2) K bits)) := by
  simp only [profile,profileWithExtras,finish,BinaryNestedFamilyMeasured.selected,BinaryNestedSecondUniformMeasured.selected,BinaryNestedBinaryAssemblyMeasured.weightsWithExtras_compat,BinaryNestedBinaryAssemblyMeasured.fromComplementWithExtras_compat,BinaryNestedBinaryAssemblyMeasured.binaryWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,BinaryNestedResidualMeasured.environmentWithExtras_compat,BinaryNestedResidualMeasured.fromEnvironmentWithExtras_compat,BinaryNestedResidualMeasured.residualWithExtras_compat,BinaryNestedFamilyMeasured.prepareWithExtras_compat,BinaryNestedFamilyMeasured.fromFamilyWithExtras_compat,BinaryNestedFamilyMeasured.lotteryWithExtras_compat,BinaryNestedSecondProfileMeasured.mixWithExtras_compat,BinaryNestedSecondProfileMeasured.profileWithExtras_compat,mixWithExtras_compat]
  try { split_ifs <;> rfl }

theorem profile_data (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input parameters K bits).1.1 = (BinaryNestedThirdProfileLifetime.profileWithTrace input parameters K bits).1 := by
  simp only [profile_record,finish,BinaryNestedThirdProfileLifetime.profileWithTrace,BinaryNestedResidualMeasured.residual_data,
    BinaryNestedResidualMeasured.pad_data,BinaryQuadraticExpressionMeasured.compare_erases]
  split_ifs <;> simp only [mix_record,BinaryNestedBinaryAssemblyMeasured.binary_data,BinaryNestedFamilyMeasured.lottery_data,
    BinaryNestedReferenceMeasured.pad_data]

def mixtureWidth (s K : ℕ) : ℕ := BinaryNestedSecondProfileMeasured.mixtureWidth s K

def workEnvelope (s K : ℕ) : ℕ := BinaryNestedResidualMeasured.workEnvelope s+20000+
  BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s 16)+
  (BinaryNestedFamilyMeasured.workEnvelope (expressionHeightBudget s 16) K+
    BinaryNestedBinaryAssemblyMeasured.workEnvelope (mixtureWidth s K)+8)+70000+16

def envelope (s K : ℕ) : ℕ := BinaryNestedResidualMeasured.envelope s+11000+
  BinaryThreeGeometryLifetime.comparisonEnvelope (2*expressionHeightBudget s 16+1)+
  (BinaryNestedFamilyMeasured.envelope (expressionHeightBudget s 16) K+
    BinaryNestedBinaryAssemblyMeasured.envelope (mixtureWidth s K)+64)+36000+128

theorem mix_bounds (alpha : SignedWord) (padded : Small) (family : (Small × Trace) × ℕ) (hA : CanonicalWord alpha)
    (W : ℕ) (hW : 1 ≤ W) (hAlpha : width alpha ≤ W)
    (hFirst : ∀ j,width (family.1.1.weight.read j) ≤ W) (hSecond : ∀ j,width (padded.weight.read j) ≤ W)
    (P U : ℕ) (hFamily : family.2 ≤ P ∧ usage family.1.2 ≤ U) :
    (mix alpha padded family).2 ≤ P+BinaryNestedBinaryAssemblyMeasured.workEnvelope W+8 ∧
      usage (mix alpha padded family).1.2 ≤ U+BinaryNestedBinaryAssemblyMeasured.envelope W+64 := by
  let assembled := BinaryNestedBinaryAssemblyMeasured.binary alpha family.1.1 padded
  have hAssembly := BinaryNestedBinaryAssemblyMeasured.binary_bounds alpha family.1.1 padded hA W hW hAlpha hFirst hSecond
  change assembled.2 ≤ _ ∧ usage assembled.1.2 ≤ _ at hAssembly
  have hw := wrap_usage 32 2 [family.1.2,assembled.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [mix_record]
  change family.2+assembled.2+8 ≤ _ ∧ usage (wrap 32 2 [family.1.2,assembled.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem finish_bounds (residual : (Residual × Trace) × ℕ) (padded : (Small × Trace) × ℕ) (guard : (Bool × Trace) × ℕ)
    (regular : Unit → (Large × Trace) × ℕ) (R P G F B U H V : ℕ)
    (hr : residual.2 ≤ R ∧ usage residual.1.2 ≤ B) (hp : padded.2 ≤ P ∧ usage padded.1.2 ≤ U)
    (hg : guard.2 ≤ G ∧ usage guard.1.2 ≤ H) (hf : (regular ()).2 ≤ F ∧ usage (regular ()).1.2 ≤ V) :
    (finish residual padded guard regular).2 ≤ R+P+G+F+70000+16 ∧
      usage (finish residual padded guard regular).1.2 ≤ B+U+H+V+36000+128 := by
  have hPad := BinaryNestedReferenceMeasured.pad_bounds padded.1.1
  unfold finish
  dsimp only
  split
  · have hw := wrap_usage 40 3 [residual.1.2,padded.1.2,guard.1.2,(regular ()).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change residual.2+padded.2+guard.2+(regular ()).2+16 ≤ _ ∧ usage (wrap 40 3 [residual.1.2,padded.1.2,guard.1.2,(regular ()).1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · have hw := wrap_usage 40 3 [residual.1.2,padded.1.2,guard.1.2,(BinaryNestedReferenceMeasured.pad padded.1.1).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change residual.2+padded.2+guard.2+(BinaryNestedReferenceMeasured.pad padded.1.1).2+16 ≤ _ ∧ usage (wrap 40 3 [residual.1.2,padded.1.2,guard.1.2,_]) ≤ _
    exact ⟨by omega,by omega⟩

theorem profile_bounds (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input parameters K bits).2 ≤ workEnvelope s K ∧ usage (profile input parameters K bits).1.2 ≤ envelope s K := by
  let residual := BinaryNestedResidualMeasured.residual input parameters
  let padded := BinaryNestedResidualMeasured.pad residual.1.1
  let family := BinaryNestedFamilyMeasured.lottery input (parameters.read 2) K bits
  let guard := BinaryQuadraticExpressionMeasured.compare (parameters.read 2) BinaryRationalOpcode.zero
  let H := expressionHeightBudget (max s (K+2)) 81
  have hResidual := BinaryNestedResidualMeasured.residual_bounds input parameters hC hParameters s hs hH
  have hPad := BinaryNestedResidualMeasured.pad_bounds residual.1.1
  have hP2C : CanonicalWord (parameters.read 2) := by rw [hParameters]; exact BinaryNestedProfileCompiler.parameters_canonical input hC 2
  have hP2H : RationalHeight (value (parameters.read 2)) (expressionHeightBudget s 16) := by
    rw [hParameters]
    exact BinaryNestedParameterWork.prepare_height input BinaryRationalOpcode.zero hC ⟨BinaryRationalOpcode.zero_valid,by decide⟩ s hs hH
      (BinaryFactoryHeight.zero_height s hs) 2
  have hFamily := BinaryNestedFamilyMeasured.lottery_bounds input (parameters.read 2) hC hP2C _
    (hs.trans (expressionHeightBudget_ge_input s 16)) (BinaryFactoryHeight.InputHeight.mono hH (expressionHeightBudget_ge_input s 16)) hP2H K bits
  have hZeroC : CanonicalWord BinaryRationalOpcode.zero := ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  have hGuard := BinaryNestedOrderMeasured.compare_bounds (parameters.read 2) BinaryRationalOpcode.zero hP2C hZeroC _ hP2H
    (BinaryFactoryHeight.zero_height _ (hs.trans (expressionHeightBudget_ge_input s 16)))
  have hResidualState := (BinaryNestedResidualMeasured.residual_data input parameters).trans
    (BinaryNestedResidualLifetime.residualWithTrace_erasure input parameters hC hParameters)
  have hPaddedState : padded.1.1 = BinarySegmentAssembly.padRight (BinaryNestedComponents.residualLottery input) 6 0 := by
    rw [BinaryNestedResidualMeasured.pad_data,BinaryNestedResidualLifetime.padWithTrace_erasure,hResidualState]
  have hFamilyState := (BinaryNestedFamilyMeasured.lottery_data input (parameters.read 2) K bits).trans
    (BinaryNestedFamilyLifetime.lotteryWithTrace_erasure input (parameters.read 2) hC hP2C K bits)
  have hFamilyC : family.1.1.Canonical := by rw [hFamilyState]; exact BinaryNestedComponents.familyLottery_canonical input _ hC hP2C K bits
  have hPaddedC : padded.1.1.Canonical := by
    rw [hPaddedState]; exact BinarySegmentAssembly.padRight_canonical _ 6 0 (BinaryNestedComponents.residualLottery_canonical input hC)
  have hFamilyH : BinaryFactoryHeight.SegmentHeight family.1.1 H := by
    rw [hFamilyState,hParameters]; exact BinaryNestedOrderedFactoryWork.family_height input hC s hs hH K bits 2
  have hPaddedH : BinaryFactoryHeight.SegmentHeight padded.1.1 H := by
    rw [hPaddedState]
    have hr := BinaryNestedRemainingFactoryWork.residual_height input hC (max s (K+2))
      (hs.trans (le_max_left _ _)) (BinaryFactoryHeight.InputHeight.mono hH (le_max_left _ _))
    exact BinaryAssemblyArithmeticWork.pad_height _ 6 0 H ((hs.trans (le_max_left _ _)).trans (expressionHeightBudget_ge_input _ 81))
      (hr.mono (expressionHeightBudget_mono _ (by decide : 24 ≤ 81)))
  have hAC : CanonicalWord (parameters.read 8) := by rw [hParameters]; exact BinaryNestedProfileCompiler.parameters_canonical input hC 8
  have hAH : RationalHeight (value (parameters.read 8)) H := by
    rw [hParameters]; exact (BinaryNestedOrderedFactoryWork.parameter_height input hC s hs hH K 8).mono
      (expressionHeightBudget_mono _ (by decide : 16 ≤ 81))
  have hAlpha : width (parameters.read 8) ≤ mixtureWidth s K := by
    have h := hAC.2.trans (rationalWordWidth_of_height hAH); unfold mixtureWidth BinaryNestedSecondProfileMeasured.mixtureWidth; omega
  have hFirst : ∀ j,width (family.1.1.weight.read j) ≤ mixtureWidth s K := by
    intro j; have h := (hFamilyC.1 j).2.trans (rationalWordWidth_of_height (hFamilyH.1 j)); unfold mixtureWidth BinaryNestedSecondProfileMeasured.mixtureWidth; omega
  have hSecond : ∀ j,width (padded.1.1.weight.read j) ≤ mixtureWidth s K := by
    intro j; have h := (hPaddedC.1 j).2.trans (rationalWordWidth_of_height (hPaddedH.1 j)); unfold mixtureWidth BinaryNestedSecondProfileMeasured.mixtureWidth; omega
  have hMix := mix_bounds (parameters.read 8) padded.1.1 family hAC _ (by unfold mixtureWidth BinaryNestedSecondProfileMeasured.mixtureWidth; omega)
    hAlpha hFirst hSecond _ _ hFamily
  have hResult := finish_bounds residual padded guard (fun _ => mix (parameters.read 8) padded.1.1 family) _ _ _ _ _ _ _ _ hResidual hPad hGuard hMix
  simp only [profile_record]
  unfold workEnvelope envelope
  with_reducible exact hResult

theorem all_prefix (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (profile input parameters K bits).1.2 steps ≤ borrowed+envelope s K ∧ framePeak ((profile input parameters K bits).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (profile_bounds input parameters hC hParameters s hs hH K bits).2 borrowed steps

end Blotto.BinaryNestedThirdProfileMeasured
