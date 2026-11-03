import Blotto.BinaryNestedFamilyLifetime
import Blotto.BinaryOrderedThreeLifetimeBound
import Blotto.BinaryNestedRemainingFactoryWork

/-! The second ordered regime's translated uniform component consumes a
supplied mirror word, so the selected caller can reuse its shared parameter
table. It traces two subtractions, the complete ordered-three factory and all
eighteen third-coordinate additions. -/
namespace Blotto.BinaryNestedSecondUniformLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev ThreeInput := BinaryThreeInputCompiler.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def preparedInput (input : Input) (mirror : SignedWord) : ThreeInput :=
  ⟨BinaryRationalOpcode.apply .sub input.M mirror,input.a,input.d,
    BinaryRationalOpcode.apply .sub input.t mirror,
    BinaryExpressionCompiler.Constant.one.word⟩

def inputWithTrace (input : Input) (mirror : SignedWord) : ThreeInput × Trace :=
  let budget := BinaryQuadraticLifetime.applyWithTrace .sub input.M mirror
  let length := BinaryQuadraticLifetime.applyWithTrace .sub input.t mirror
  (⟨budget.1,input.a,input.d,length.1,BinaryExpressionCompiler.Constant.one.word⟩,
    wrap 32 2 [budget.2,length.2])

theorem inputWithTrace_erasure (input : Input) (mirror : SignedWord)
    (hC : input.Canonical) (hMirror : CanonicalWord mirror) :
    (inputWithTrace input mirror).1 = preparedInput input mirror := by
  simp only [inputWithTrace,preparedInput,
    BinaryQuadraticLifetime.applyWithTrace_state .sub _ _ hC.1.1 hMirror.1,
    BinaryQuadraticLifetime.applyWithTrace_state .sub _ _ hC.2.2.2.2.1.1 hMirror.1]

theorem preparedInput_canonical (input : Input) (mirror : SignedWord)
    (hC : input.Canonical) (hMirror : CanonicalWord mirror) :
    (preparedInput input mirror).Canonical :=
  ⟨BinaryReflectedFourSetup.opcode_canonical .sub _ _ hC.1 hMirror,
    hC.2.1,hC.2.2.1,
    BinaryReflectedFourSetup.opcode_canonical .sub _ _ hC.2.2.2.2.1 hMirror,
    BinaryExpressionCompiler.Constant.word_canonical .one⟩

theorem preparedInput_height (input : Input) (mirror : SignedWord)
    (hC : input.Canonical) (hMirror : CanonicalWord mirror)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hMirrorH : RationalHeight (value mirror) s) :
    BinaryOrderedThreeFactoryWork.InputHeight (preparedInput input mirror)
      (expressionHeightBudget s 1) := by
  have hm := expressionHeightBudget_ge_input s 1
  have hBudget : RationalHeight (value (BinaryRationalOpcode.apply .sub input.M mirror))
      (expressionHeightBudget s 1) := by
    rw [BinaryRationalOpcode.apply_value .sub _ _ hC.1.1 hMirror.1]
    have hFirst : RationalHeight (value input.M) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hH.1
    have hSecond : RationalHeight (value mirror) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hMirrorH
    change RationalHeight (value input.M - value mirror) (expressionHeightBudget s 1)
    simpa only [expressionHeightBudget_zero,expressionHeightBudget_comp] using
      hFirst.sub_level hSecond
  have hLength : RationalHeight (value (BinaryRationalOpcode.apply .sub input.t mirror))
      (expressionHeightBudget s 1) := by
    rw [BinaryRationalOpcode.apply_value .sub _ _ hC.2.2.2.2.1.1 hMirror.1]
    have hFirst : RationalHeight (value input.t) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hH.2.2.2.2.1
    have hSecond : RationalHeight (value mirror) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hMirrorH
    change RationalHeight (value input.t - value mirror) (expressionHeightBudget s 1)
    simpa only [expressionHeightBudget_zero,expressionHeightBudget_comp] using
      hFirst.sub_level hSecond
  exact ⟨hBudget,hH.2.1.mono hm,hH.2.2.1.mono hm,hLength,
    BinaryFactoryHeight.one_height _ (hs.trans hm)⟩

def inputEnvelope (s : ℕ) : ℕ := 2 * opcodeEnvelope (2 * s + 1) + 128

theorem inputWithTrace_usage (input : Input) (mirror : SignedWord)
    (hC : input.Canonical) (hMirror : CanonicalWord mirror)
    (s : ℕ) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hMirrorH : RationalHeight (value mirror) s) :
    usage (inputWithTrace input mirror).2 ≤ inputEnvelope s := by
  have hM : width input.M ≤ 2 * s + 1 := by
    have h := hC.1.2.trans (rationalWordWidth_of_height hH.1)
    omega
  have hT : width input.t ≤ 2 * s + 1 := by
    have h := hC.2.2.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.2.2.1)
    omega
  have hR : width mirror ≤ 2 * s + 1 := by
    have h := hMirror.2.trans (rationalWordWidth_of_height hMirrorH)
    omega
  have hb := opcode_usage .sub input.M mirror (2*s+1) hM hR
  have hl := opcode_usage .sub input.t mirror (2*s+1) hT hR
  have hw := wrap_usage 32 2
    [(BinaryQuadraticLifetime.applyWithTrace .sub input.M mirror).2,
      (BinaryQuadraticLifetime.applyWithTrace .sub input.t mirror).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [(BinaryQuadraticLifetime.applyWithTrace .sub input.M mirror).2,
      (BinaryQuadraticLifetime.applyWithTrace .sub input.t mirror).2]) ≤ _
  unfold inputEnvelope
  omega

def uniformWithTrace (input : Input) (mirror : SignedWord) : Segment × Trace :=
  let prepared := inputWithTrace input mirror
  let child := BinaryOrderedThreeLifetime.descriptorWithTrace prepared.1
  let shifted := BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace child.1 mirror
  (shifted.1,wrap 40 3 [prepared.2,child.2,shifted.2])

theorem uniformWithTrace_erasure (input : Input) (mirror : SignedWord)
    (hC : input.Canonical) (hMirror : CanonicalWord mirror) :
    (uniformWithTrace input mirror).1 =
      BinarySegmentAssembly.shiftThird
        (BinaryThreeInputCompiler.descriptor (preparedInput input mirror)) mirror := by
  have hPrepared := inputWithTrace_erasure input mirror hC hMirror
  have hPreparedC : (inputWithTrace input mirror).1.Canonical := by
    rw [hPrepared]
    exact preparedInput_canonical input mirror hC hMirror
  have hChild := BinaryOrderedThreeLifetime.descriptorWithTrace_erasure
    (inputWithTrace input mirror).1 hPreparedC
  have hChildC : (BinaryOrderedThreeLifetime.descriptorWithTrace
      (inputWithTrace input mirror).1).1.Canonical := by
    rw [hChild]
    exact BinaryThreeInputCompiler.descriptor_canonical _ hPreparedC
  have hShift := BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace_erasure
    (BinaryOrderedThreeLifetime.descriptorWithTrace
      (inputWithTrace input mirror).1).1 mirror hChildC hMirror
  unfold uniformWithTrace
  dsimp only
  rw [hShift,hChild,hPrepared]

def envelope (s : ℕ) : ℕ :=
  let H := expressionHeightBudget s 1
  let T := expressionHeightBudget H 18
  inputEnvelope s + BinaryOrderedThreeLifetimeBound.envelope H +
    BinaryNestedFirstAssemblyLifetime.shiftEnvelope (2 * T + 1) + 256

theorem uniformWithTrace_usage (input : Input) (mirror : SignedWord)
    (hC : input.Canonical) (hMirror : CanonicalWord mirror)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hMirrorH : RationalHeight (value mirror) s) :
    usage (uniformWithTrace input mirror).2 ≤ envelope s := by
  let H := expressionHeightBudget s 1
  let T := expressionHeightBudget H 18
  let prepared := inputWithTrace input mirror
  let child := BinaryOrderedThreeLifetime.descriptorWithTrace prepared.1
  have hPrepared := inputWithTrace_usage input mirror hC hMirror s hH hMirrorH
  change usage prepared.2 ≤ _ at hPrepared
  have hPreparedState := inputWithTrace_erasure input mirror hC hMirror
  change prepared.1 = _ at hPreparedState
  have hPreparedC : prepared.1.Canonical := by
    rw [hPreparedState]
    exact preparedInput_canonical input mirror hC hMirror
  have hPreparedH : BinaryOrderedThreeFactoryWork.InputHeight prepared.1 H := by
    rw [hPreparedState]
    exact preparedInput_height input mirror hC hMirror s hs hH hMirrorH
  have hsH : 3 ≤ H := hs.trans (expressionHeightBudget_ge_input s 1)
  have hChild := BinaryOrderedThreeLifetimeBound.descriptorWithTrace_usage
    prepared.1 hPreparedC H hsH hPreparedH
  change usage child.2 ≤ _ at hChild
  change usage child.2 ≤
    BinaryOrderedThreeLifetimeBound.envelope (expressionHeightBudget s 1) at hChild
  have hChildState := BinaryOrderedThreeLifetime.descriptorWithTrace_erasure
    prepared.1 hPreparedC
  have hChildC : child.1.Canonical := by
    rw [hChildState]
    exact BinaryThreeInputCompiler.descriptor_canonical _ hPreparedC
  have hChildH : BinaryFactoryHeight.SegmentHeight child.1 T := by
    rw [hChildState]
    exact BinaryOrderedThreeFactoryWork.descriptor_height prepared.1
      hPreparedC H hsH hPreparedH
  have hMirrorW : width mirror ≤ 2*T+1 := by
    have h := hMirror.2.trans (rationalWordWidth_of_height hMirrorH)
    have hm := (expressionHeightBudget_ge_input s 1).trans
      (expressionHeightBudget_ge_input H 18)
    dsimp only [H,T] at hm ⊢
    omega
  have hP : ∀ slot,width ((child.1.P.read slot).read 2) ≤ 2*T+1 := by
    intro slot
    have h := (hChildC.2.1 slot 2).2.trans
      (rationalWordWidth_of_height (hChildH.2 slot 2).1)
    omega
  have hQ : ∀ slot,width ((child.1.Q.read slot).read 2) ≤ 2*T+1 := by
    intro slot
    have h := (hChildC.2.2 slot 2).2.trans
      (rationalWordWidth_of_height (hChildH.2 slot 2).2)
    omega
  have hShift := BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace_usage
    child.1 mirror (2*T+1) hP hQ hMirrorW
  change usage (BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace child.1 mirror).2 ≤
    BinaryNestedFirstAssemblyLifetime.shiftEnvelope
      (2 * expressionHeightBudget (expressionHeightBudget s 1) 18 + 1) at hShift
  have hw := wrap_usage 40 3
    [prepared.2,child.2,
      (BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace child.1 mirror).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 40 3
    [prepared.2,child.2,
      (BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace child.1 mirror).2]) ≤ _
  unfold envelope
  dsimp only [H,T] at hChild ⊢
  omega

theorem all_prefix (input : Input) (mirror : SignedWord)
    (hC : input.Canonical) (hMirror : CanonicalWord mirror)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (hMirrorH : RationalHeight (value mirror) s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (uniformWithTrace input mirror).2 steps ≤ borrowed + envelope s ∧
    framePeak ((uniformWithTrace input mirror).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (uniformWithTrace_usage input mirror hC hMirror s hs hH hMirrorH) borrowed steps

def selectedWithTrace (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    Segment × Trace := uniformWithTrace input (parameters.read 6)

theorem selectedWithTrace_erasure (input : Input)
    (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input) :
    (selectedWithTrace input parameters).1 = BinaryNestedComponents.secondUniformLottery input := by
  subst parameters
  have hMirror := BinaryNestedComponents.mirror_canonical input hC
  unfold selectedWithTrace BinaryNestedComponents.secondUniformLottery
    BinaryNestedComponents.secondUniformInput BinaryNestedComponents.mirror
  simpa only [BinaryNestedProfileCompiler.parameters,preparedInput] using
    uniformWithTrace_erasure input
      ((BinaryNestedParameters.prepare input BinaryRationalOpcode.zero).read 6) hC hMirror

theorem selectedWithTrace_usage (input : Input)
    (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (selectedWithTrace input parameters).2 ≤ envelope (expressionHeightBudget s 16) := by
  subst parameters
  let H := expressionHeightBudget s 16
  have hMirrorC := BinaryNestedComponents.mirror_canonical input hC
  have hMirrorH := BinaryNestedRemainingFactoryWork.mirror_height input hC s hs hH
  have hInputH : BinaryNestedParameterWork.InputHeight input H :=
    BinaryFactoryHeight.InputHeight.mono hH (expressionHeightBudget_ge_input s 16)
  have hsH : 3 ≤ H := hs.trans (expressionHeightBudget_ge_input s 16)
  change usage (uniformWithTrace input (BinaryNestedComponents.mirror input)).2 ≤ _
  exact uniformWithTrace_usage input (BinaryNestedComponents.mirror input)
    hC hMirrorC H hsH hInputH hMirrorH

theorem selected_all_prefix (input : Input)
    (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (selectedWithTrace input parameters).2 steps ≤
      borrowed + envelope (expressionHeightBudget s 16) ∧
    framePeak ((selectedWithTrace input parameters).2.take steps) ≤
      envelope (expressionHeightBudget s 16) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (selectedWithTrace_usage input parameters hC hParameters s hs hH) borrowed steps

end Blotto.BinaryNestedSecondUniformLifetime
