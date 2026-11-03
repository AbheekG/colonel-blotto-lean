import Blotto.BinaryNestedFamilyMeasured
import Blotto.BinaryNestedBinaryAssemblyMeasured
import Blotto.BinaryNestedSecondProfileLifetime

/-! The second interior profile consumes the shared parameters, one actual
measured family and strict mirror guard, then only the reached measured
translated-uniform mixture or family padding. Original fields derive prices. -/
namespace Blotto.BinaryNestedSecondProfileMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1500000

abbrev Input := BinaryNestedParameters.Input
abbrev Small := BinaryStoredOverlapEnvironment.Segment 3 9
abbrev Large := BinaryStoredOverlapEnvironment.Segment 3 18

set_option cleanup.letToHave false in
def mixWithExtras (alpha : SignedWord) (family : Small) (uniform : (Small × Trace) × ℕ) : ((Large × Trace) × ℕ) × ℕ :=
  let assembled := BinaryNestedBinaryAssemblyMeasured.binaryWithExtras alpha family uniform.1.1
  (((assembled.1.1.1,wrap 32 2 [uniform.1.2,assembled.1.1.2]),uniform.2+assembled.1.2+8),assembled.2)

def mix (alpha : SignedWord) (family : Small) (uniform : (Small × Trace) × ℕ) : (Large × Trace) × ℕ :=
  (mixWithExtras alpha family uniform).1

theorem mixWithExtras_compat (alpha : SignedWord) (family : Small) (uniform : (Small × Trace) × ℕ) :
    (mixWithExtras alpha family uniform).1 = mix alpha family uniform := rfl

theorem mix_record (alpha : SignedWord) (family : Small) (uniform : (Small × Trace) × ℕ) :
    mix alpha family uniform =
  let assembled := BinaryNestedBinaryAssemblyMeasured.binary alpha family uniform.1.1
  ((assembled.1.1,wrap 32 2 [uniform.1.2,assembled.1.2]),uniform.2+assembled.2+8) := by
  simp only [mix,mixWithExtras,BinaryNestedBinaryAssemblyMeasured.weightsWithExtras_compat,BinaryNestedBinaryAssemblyMeasured.fromComplementWithExtras_compat,BinaryNestedBinaryAssemblyMeasured.binaryWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,BinaryNestedSecondUniformMeasured.prepareWithExtras_compat,BinaryNestedSecondUniformMeasured.fromPreparedWithExtras_compat,BinaryNestedSecondUniformMeasured.uniformWithExtras_compat,BinaryNestedFamilyMeasured.prepareWithExtras_compat,BinaryNestedFamilyMeasured.fromFamilyWithExtras_compat,BinaryNestedFamilyMeasured.lotteryWithExtras_compat]
  try { split_ifs <;> rfl }

def finish (family : (Small × Trace) × ℕ) (guard : (Bool × Trace) × ℕ)
    (regular : Unit → (Large × Trace) × ℕ) : (Large × Trace) × ℕ :=
  let chosen := if !guard.1.1 then regular () else BinaryNestedReferenceMeasured.pad family.1.1
  ((chosen.1.1,wrap 40 3 [family.1.2,guard.1.2,chosen.1.2]),family.2+guard.2+chosen.2+12)

set_option cleanup.letToHave false in
def profileWithExtras (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : ((Large × Trace) × ℕ) × ℕ :=
  let family := BinaryNestedFamilyMeasured.lotteryWithExtras input (parameters.read 6) K bits
  let guard := BinaryQuadraticExpressionMeasured.compare input.t (parameters.read 6)
  let chosen := if !guard.1.1 then
      let uniform := BinaryNestedSecondUniformMeasured.uniformWithExtras input (parameters.read 6)
      let assembled := mixWithExtras (parameters.read 7) family.1.1.1 uniform.1
      (assembled.1,uniform.2+assembled.2)
    else (BinaryNestedReferenceMeasured.pad family.1.1.1,0)
  (((chosen.1.1.1,wrap 40 3 [family.1.1.2,guard.1.2,chosen.1.1.2]),family.1.2+guard.2+chosen.1.2+12),family.2+chosen.2)

def profile (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : (Large × Trace) × ℕ :=
  (profileWithExtras input parameters K bits).1

theorem profileWithExtras_compat (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithExtras input parameters K bits).1 = profile input parameters K bits := rfl

attribute [local irreducible] BinaryNestedFamilyMeasured.lotteryWithExtras BinaryNestedSecondUniformMeasured.uniformWithExtras mixWithExtras

theorem profile_record (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    profile input parameters K bits =
  let family := BinaryNestedFamilyMeasured.selected input parameters K bits
  let guard := BinaryQuadraticExpressionMeasured.compare input.t (parameters.read 6)
  finish family guard (fun _ => mix (parameters.read 7) family.1.1 (BinaryNestedSecondUniformMeasured.selected input parameters)) := by
  simp only [profile,profileWithExtras,finish,BinaryNestedFamilyMeasured.selected,BinaryNestedSecondUniformMeasured.selected,BinaryNestedBinaryAssemblyMeasured.weightsWithExtras_compat,BinaryNestedBinaryAssemblyMeasured.fromComplementWithExtras_compat,BinaryNestedBinaryAssemblyMeasured.binaryWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,BinaryNestedSecondUniformMeasured.prepareWithExtras_compat,BinaryNestedSecondUniformMeasured.fromPreparedWithExtras_compat,BinaryNestedSecondUniformMeasured.uniformWithExtras_compat,BinaryNestedFamilyMeasured.prepareWithExtras_compat,BinaryNestedFamilyMeasured.fromFamilyWithExtras_compat,BinaryNestedFamilyMeasured.lotteryWithExtras_compat,mixWithExtras_compat]
  try { split_ifs <;> rfl }

theorem profile_data (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input parameters K bits).1.1 = (BinaryNestedSecondProfileLifetime.profileWithTrace input parameters K bits).1 := by
  simp only [profile_record,finish,BinaryNestedSecondProfileLifetime.profileWithTrace,BinaryNestedFamilyMeasured.selected_data,
    BinaryQuadraticExpressionMeasured.compare_erases]
  split_ifs <;> simp only [mix_record,BinaryNestedBinaryAssemblyMeasured.binary_data,BinaryNestedSecondUniformMeasured.selected_data,
    BinaryNestedReferenceMeasured.pad_data]

def mixtureWidth (s K : ℕ) : ℕ := 2*expressionHeightBudget (max s (K+2)) 81+1

def workEnvelope (s K : ℕ) : ℕ := BinaryNestedFamilyMeasured.workEnvelope (expressionHeightBudget s 16) K+
  BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s 16)+
  (BinaryNestedSecondUniformMeasured.workEnvelope (expressionHeightBudget s 16)+
    BinaryNestedBinaryAssemblyMeasured.workEnvelope (mixtureWidth s K)+8)+70000+12

def envelope (s K : ℕ) : ℕ := BinaryNestedFamilyMeasured.envelope (expressionHeightBudget s 16) K+
  BinaryThreeGeometryLifetime.comparisonEnvelope (2*expressionHeightBudget s 16+1)+
  (BinaryNestedSecondUniformMeasured.envelope (expressionHeightBudget s 16)+
    BinaryNestedBinaryAssemblyMeasured.envelope (mixtureWidth s K)+64)+36000+96

theorem mix_bounds (alpha : SignedWord) (family : Small) (uniform : (Small × Trace) × ℕ) (hA : CanonicalWord alpha)
    (W : ℕ) (hW : 1 ≤ W) (hAlpha : width alpha ≤ W)
    (hFirst : ∀ j,width (family.weight.read j) ≤ W) (hSecond : ∀ j,width (uniform.1.1.weight.read j) ≤ W)
    (P U : ℕ) (hUniform : uniform.2 ≤ P ∧ usage uniform.1.2 ≤ U) :
    (mix alpha family uniform).2 ≤ P+BinaryNestedBinaryAssemblyMeasured.workEnvelope W+8 ∧
    usage (mix alpha family uniform).1.2 ≤ U+BinaryNestedBinaryAssemblyMeasured.envelope W+64 := by
  let assembled := BinaryNestedBinaryAssemblyMeasured.binary alpha family uniform.1.1
  have hAssembly := BinaryNestedBinaryAssemblyMeasured.binary_bounds alpha family uniform.1.1 hA W hW hAlpha hFirst hSecond
  change assembled.2 ≤ _ ∧ usage assembled.1.2 ≤ _ at hAssembly
  have hw := wrap_usage 32 2 [uniform.1.2,assembled.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [mix_record]
  change uniform.2+assembled.2+8 ≤ _ ∧ usage (wrap 32 2 [uniform.1.2,assembled.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem finish_bounds (family : (Small × Trace) × ℕ) (guard : (Bool × Trace) × ℕ)
    (regular : Unit → (Large × Trace) × ℕ) (F G R B U H : ℕ)
    (hf : family.2 ≤ F ∧ usage family.1.2 ≤ B) (hg : guard.2 ≤ G ∧ usage guard.1.2 ≤ U)
    (hr : (regular ()).2 ≤ R ∧ usage (regular ()).1.2 ≤ H) :
    (finish family guard regular).2 ≤ F+G+R+70000+12 ∧ usage (finish family guard regular).1.2 ≤ B+U+H+36000+96 := by
  have hp := BinaryNestedReferenceMeasured.pad_bounds family.1.1
  unfold finish
  dsimp only
  split
  · have hw := wrap_usage 40 3 [family.1.2,guard.1.2,(regular ()).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change family.2+guard.2+(regular ()).2+12 ≤ _ ∧ usage (wrap 40 3 [family.1.2,guard.1.2,(regular ()).1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · have hw := wrap_usage 40 3 [family.1.2,guard.1.2,(BinaryNestedReferenceMeasured.pad family.1.1).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change family.2+guard.2+(BinaryNestedReferenceMeasured.pad family.1.1).2+12 ≤ _ ∧ usage (wrap 40 3 [family.1.2,guard.1.2,_]) ≤ _
    exact ⟨by omega,by omega⟩

theorem profile_bounds (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    (profile input parameters K bits).2 ≤ workEnvelope s K ∧ usage (profile input parameters K bits).1.2 ≤ envelope s K := by
  let family := BinaryNestedFamilyMeasured.selected input parameters K bits
  let uniform := BinaryNestedSecondUniformMeasured.selected input parameters
  let guard := BinaryQuadraticExpressionMeasured.compare input.t (parameters.read 6)
  let H := expressionHeightBudget (max s (K+2)) 81
  have hFamily := BinaryNestedFamilyMeasured.selected_bounds input parameters hC hParameters s hs hH K bits
  have hUniform := BinaryNestedSecondUniformMeasured.selected_bounds input parameters hC hParameters s hs hH
  have hMirrorC : CanonicalWord (parameters.read 6) := by rw [hParameters]; exact BinaryNestedComponents.mirror_canonical input hC
  have hMirrorH : RationalHeight (value (parameters.read 6)) (expressionHeightBudget s 16) := by
    rw [hParameters]; exact BinaryNestedRemainingFactoryWork.mirror_height input hC s hs hH
  have hGuard := BinaryNestedOrderMeasured.compare_bounds input.t (parameters.read 6) hC.2.2.2.2.1 hMirrorC _
    (hH.2.2.2.2.1.mono (expressionHeightBudget_ge_input s 16)) hMirrorH
  have hFamilyState := (BinaryNestedFamilyMeasured.selected_data input parameters K bits).trans
    (BinaryNestedFamilyLifetime.selectedWithTrace_erasure input parameters hC hParameters K bits)
  have hUniformState := (BinaryNestedSecondUniformMeasured.selected_data input parameters).trans
    (BinaryNestedSecondUniformLifetime.selectedWithTrace_erasure input parameters hC hParameters)
  have hFamilyC : family.1.1.Canonical := by
    rw [hFamilyState]; exact BinaryNestedComponents.familyLottery_canonical input _ hC (BinaryNestedComponents.mirror_canonical input hC) K bits
  have hUniformC : uniform.1.1.Canonical := by rw [hUniformState]; exact BinaryNestedComponents.secondUniformLottery_canonical input hC
  have hFamilyH : BinaryFactoryHeight.SegmentHeight family.1.1 H := by
    rw [hFamilyState]; exact BinaryNestedOrderedFactoryWork.family_height input hC s hs hH K bits 6
  have hUniformH : BinaryFactoryHeight.SegmentHeight uniform.1.1 H := by
    rw [hUniformState]
    exact (BinaryNestedRemainingFactoryWork.second_height input hC (max s (K+2)) (hs.trans (le_max_left _ _))
      (BinaryFactoryHeight.InputHeight.mono hH (le_max_left _ _))).mono (expressionHeightBudget_mono _ (by decide : 36 ≤ 81))
  have hAC : CanonicalWord (parameters.read 7) := by rw [hParameters]; exact BinaryNestedProfileCompiler.parameters_canonical input hC 7
  have hAH : RationalHeight (value (parameters.read 7)) H := by
    rw [hParameters]
    exact (BinaryNestedOrderedFactoryWork.parameter_height input hC s hs hH K 7).mono (expressionHeightBudget_mono _ (by decide : 16 ≤ 81))
  have hAlpha : width (parameters.read 7) ≤ mixtureWidth s K := by
    have h := hAC.2.trans (rationalWordWidth_of_height hAH); unfold mixtureWidth; omega
  have hFirst : ∀ j,width (family.1.1.weight.read j) ≤ mixtureWidth s K := by
    intro j; have h := (hFamilyC.1 j).2.trans (rationalWordWidth_of_height (hFamilyH.1 j)); unfold mixtureWidth; omega
  have hSecond : ∀ j,width (uniform.1.1.weight.read j) ≤ mixtureWidth s K := by
    intro j; have h := (hUniformC.1 j).2.trans (rationalWordWidth_of_height (hUniformH.1 j)); unfold mixtureWidth; omega
  have hMix := mix_bounds (parameters.read 7) family.1.1 uniform hAC _ (by unfold mixtureWidth; omega) hAlpha hFirst hSecond _ _ hUniform
  have hResult := finish_bounds family guard (fun _ => mix (parameters.read 7) family.1.1 uniform) _ _ _ _ _ _ hFamily hGuard hMix
  simp only [profile_record]
  unfold workEnvelope envelope
  with_reducible exact hResult

theorem all_prefix (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (profile input parameters K bits).1.2 steps ≤ borrowed+envelope s K ∧
      framePeak ((profile input parameters K bits).1.2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (profile_bounds input parameters hC hParameters s hs hH K bits).2 borrowed steps

end Blotto.BinaryNestedSecondProfileMeasured
