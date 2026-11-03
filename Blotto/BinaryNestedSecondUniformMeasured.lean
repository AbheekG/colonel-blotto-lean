import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryNestedFirstAssemblyMeasured
import Blotto.BinaryThreeFactoryMeasured
import Blotto.BinaryNestedSecondUniformLifetime

/-! Two actual measured subtractions feed the ordered-three factory and
measured third-coordinate translation. A supplied mirror word shares the
caller's actual parameter table. Original heights derive all component prices. -/
namespace Blotto.BinaryNestedSecondUniformMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 1200000

abbrev Input := BinaryNestedParameters.Input
abbrev ThreeInput := BinaryThreeInputCompiler.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def collectInput (input : Input) (budget length : (SignedWord × Trace) × ℕ) : (ThreeInput × Trace) × ℕ :=
  ((⟨budget.1.1,input.a,input.d,length.1.1,BinaryExpressionCompiler.Constant.one.word⟩,
    wrap 32 2 [budget.1.2,length.1.2]),budget.2+length.2+8)

set_option cleanup.letToHave false in
def prepareWithExtras (input : Input) (mirror : SignedWord) : ((ThreeInput × Trace) × ℕ) × ℕ :=
  let budget := BinaryNormalizedCoordinate.opcode .sub input.M mirror
  let length := BinaryNormalizedCoordinate.opcode .sub input.t mirror
  (collectInput input budget.1 length.1,budget.2+length.2)

def prepare (input : Input) (mirror : SignedWord) : (ThreeInput × Trace) × ℕ :=
  (prepareWithExtras input mirror).1

theorem prepareWithExtras_compat (input : Input) (mirror : SignedWord) :
    (prepareWithExtras input mirror).1 = prepare input mirror := rfl

theorem prepare_record (input : Input) (mirror : SignedWord) :
    prepare input mirror =
  collectInput input (BinaryPlannedQuadratic.apply .sub input.M mirror) (BinaryPlannedQuadratic.apply .sub input.t mirror) := by
  simp only [prepare,prepareWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record]

theorem prepare_data (input : Input) (mirror : SignedWord) :
    (prepare input mirror).1.1 = (BinaryNestedSecondUniformLifetime.inputWithTrace input mirror).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,prepare_record,collectInput,BinaryNestedSecondUniformLifetime.inputWithTrace,BinaryQuadraticMeasured.apply_erases]

def inputPrice (s : ℕ) : ℕ := 2*BinaryReflectedSystemMeasured.opcodePrice (2*s+1)+8
def inputEnvelope (s : ℕ) : ℕ := 2*opcodeEnvelope (2*s+1)+64

theorem collectInput_bounds (input : Input) (budget length : (SignedWord × Trace) × ℕ) (P U : ℕ)
    (hb : budget.2 ≤ P ∧ usage budget.1.2 ≤ U) (hl : length.2 ≤ P ∧ usage length.1.2 ≤ U) :
    (collectInput input budget length).2 ≤ 2*P+8 ∧ usage (collectInput input budget length).1.2 ≤ 2*U+64 := by
  have hw := wrap_usage 32 2 [budget.1.2,length.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change budget.2+length.2+8 ≤ _ ∧ usage (wrap 32 2 [budget.1.2,length.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem prepare_bounds (input : Input) (mirror : SignedWord) (hC : input.Canonical) (hM : CanonicalWord mirror)
    (s : ℕ) (hH : BinaryNestedParameterWork.InputHeight input s) (hMH : RationalHeight (value mirror) s) :
    (prepare input mirror).2 ≤ inputPrice s ∧ usage (prepare input mirror).1.2 ≤ inputEnvelope s := by
  have hB : width input.M ≤ 2*s+1 := by have h := hC.1.2.trans (rationalWordWidth_of_height hH.1); omega
  have hT : width input.t ≤ 2*s+1 := by have h := hC.2.2.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.2.2.1); omega
  have hMirror : width mirror ≤ 2*s+1 := by have h := hM.2.trans (rationalWordWidth_of_height hMH); omega
  simp only [prepare_record, BinaryPlannedQuadratic.apply_previous]
  exact collectInput_bounds input _ _ _ _
    (BinaryReflectedSystemMeasured.opcode_bounds .sub _ _ _ hB hMirror)
    (BinaryReflectedSystemMeasured.opcode_bounds .sub _ _ _ hT hMirror)

def collect (prepared : (ThreeInput × Trace) × ℕ) (child shifted : (Segment × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  ((shifted.1.1,wrap 40 3 [prepared.1.2,child.1.2,shifted.1.2]),prepared.2+child.2+shifted.2+12)

set_option cleanup.letToHave false in
def fromPreparedWithExtras (prepared : (ThreeInput × Trace) × ℕ) (mirror : SignedWord) : ((Segment × Trace) × ℕ) × ℕ :=
  let child := BinaryThreeFactoryMeasured.orderedWithExtras prepared.1.1
  let shifted := BinaryNestedFirstAssemblyMeasured.shiftWithExtras child.1.1.1 mirror
  (collect prepared child.1 shifted.1,child.2+shifted.2)

def fromPrepared (prepared : (ThreeInput × Trace) × ℕ) (mirror : SignedWord) : (Segment × Trace) × ℕ :=
  (fromPreparedWithExtras prepared mirror).1

theorem fromPreparedWithExtras_compat (prepared : (ThreeInput × Trace) × ℕ) (mirror : SignedWord) :
    (fromPreparedWithExtras prepared mirror).1 = fromPrepared prepared mirror := rfl

theorem fromPrepared_record (prepared : (ThreeInput × Trace) × ℕ) (mirror : SignedWord) :
    fromPrepared prepared mirror =
  let child := BinaryThreeFactoryMeasured.ordered prepared.1.1
  let shifted := BinaryNestedFirstAssemblyMeasured.shift child.1.1 mirror
  collect prepared child shifted := by
  simp only [fromPrepared,fromPreparedWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryThreeFactoryMeasured.orderedWithExtras_compat,BinaryThreeFactoryMeasured.descriptorWithExtras_compat,BinaryNestedFirstAssemblyMeasured.shiftWithExtras_compat,BinaryReflectedSystemMeasured.capacityWithExtras_compat,BinaryReflectedSystemMeasured.fromParametersWithExtras_compat]

set_option cleanup.letToHave false in
def uniformWithExtras (input : Input) (mirror : SignedWord) : ((Segment × Trace) × ℕ) × ℕ :=
  let prepared := prepareWithExtras input mirror
  let produced := fromPreparedWithExtras prepared.1 mirror
  (produced.1,prepared.2+produced.2)

def uniform (input : Input) (mirror : SignedWord) : (Segment × Trace) × ℕ :=
  (uniformWithExtras input mirror).1

theorem uniformWithExtras_compat (input : Input) (mirror : SignedWord) :
    (uniformWithExtras input mirror).1 = uniform input mirror := rfl

theorem uniform_record (input : Input) (mirror : SignedWord) :
    uniform input mirror = fromPrepared (prepare input mirror) mirror := by
  simp only [prepareWithExtras_compat,uniform,uniformWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryThreeFactoryMeasured.orderedWithExtras_compat,BinaryThreeFactoryMeasured.descriptorWithExtras_compat,BinaryNestedFirstAssemblyMeasured.shiftWithExtras_compat,BinaryReflectedSystemMeasured.capacityWithExtras_compat,BinaryReflectedSystemMeasured.fromParametersWithExtras_compat,fromPreparedWithExtras_compat]

theorem uniform_data (input : Input) (mirror : SignedWord) :
    (uniform input mirror).1.1 = (BinaryNestedSecondUniformLifetime.uniformWithTrace input mirror).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,uniform_record,fromPrepared_record,collect,BinaryNestedSecondUniformLifetime.uniformWithTrace,
    BinaryNestedFirstAssemblyMeasured.shift_data,BinaryThreeFactoryMeasured.ordered_data,prepare_data]

def shiftWidth (H : ℕ) : ℕ := 2*expressionHeightBudget H 18+1

def workEnvelope (s : ℕ) : ℕ := inputPrice s+BinaryThreeFactoryMeasured.orderedWork (expressionHeightBudget s 1)+
  BinaryNestedFirstAssemblyMeasured.shiftPrice (shiftWidth (expressionHeightBudget s 1))+12

def envelope (s : ℕ) : ℕ := inputEnvelope s+BinaryThreeFactoryMeasured.orderedEnvelope (expressionHeightBudget s 1)+
  BinaryNestedFirstAssemblyMeasured.shiftEnvelope (shiftWidth (expressionHeightBudget s 1))+64

theorem collect_bounds (prepared : (ThreeInput × Trace) × ℕ) (child shifted : (Segment × Trace) × ℕ)
    (P C S B U F : ℕ) (hp : prepared.2 ≤ P ∧ usage prepared.1.2 ≤ B)
    (hc : child.2 ≤ C ∧ usage child.1.2 ≤ U) (hs : shifted.2 ≤ S ∧ usage shifted.1.2 ≤ F) :
    (collect prepared child shifted).2 ≤ P+C+S+12 ∧ usage (collect prepared child shifted).1.2 ≤ B+U+F+64 := by
  have hw := wrap_usage 40 3 [prepared.1.2,child.1.2,shifted.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change prepared.2+child.2+shifted.2+12 ≤ _ ∧ usage (wrap 40 3 [prepared.1.2,child.1.2,shifted.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem fromPrepared_bounds (prepared : (ThreeInput × Trace) × ℕ) (mirror : SignedWord)
    (hC : prepared.1.1.Canonical) (H : ℕ) (hH : 3 ≤ H)
    (hHeight : BinaryOrderedThreeFactoryWork.InputHeight prepared.1.1 H) (hMirror : width mirror ≤ shiftWidth H)
    (P U : ℕ) (hPrepared : prepared.2 ≤ P ∧ usage prepared.1.2 ≤ U) :
    (fromPrepared prepared mirror).2 ≤ P+BinaryThreeFactoryMeasured.orderedWork H+BinaryNestedFirstAssemblyMeasured.shiftPrice (shiftWidth H)+12 ∧
    usage (fromPrepared prepared mirror).1.2 ≤ U+BinaryThreeFactoryMeasured.orderedEnvelope H+BinaryNestedFirstAssemblyMeasured.shiftEnvelope (shiftWidth H)+64 := by
  let child := BinaryThreeFactoryMeasured.ordered prepared.1.1
  let shifted := BinaryNestedFirstAssemblyMeasured.shift child.1.1 mirror
  have hState := (BinaryThreeFactoryMeasured.ordered_data prepared.1.1).trans
    (BinaryOrderedThreeLifetime.descriptorWithTrace_erasure prepared.1.1 hC)
  have hChildC : child.1.1.Canonical := by rw [hState]; exact BinaryThreeInputCompiler.descriptor_canonical _ hC
  have hChildH : BinaryFactoryHeight.SegmentHeight child.1.1 (expressionHeightBudget H 18) := by
    rw [hState]; exact BinaryOrderedThreeFactoryWork.descriptor_height prepared.1.1 hC H hH hHeight
  have hP : ∀ slot,width ((child.1.1.P.read slot).read 2) ≤ shiftWidth H := by
    intro slot; have h := (hChildC.2.1 slot 2).2.trans (rationalWordWidth_of_height (hChildH.2 slot 2).1)
    unfold shiftWidth; omega
  have hQ : ∀ slot,width ((child.1.1.Q.read slot).read 2) ≤ shiftWidth H := by
    intro slot; have h := (hChildC.2.2 slot 2).2.trans (rationalWordWidth_of_height (hChildH.2 slot 2).2)
    unfold shiftWidth; omega
  have hChild := And.intro (BinaryThreeFactoryMeasured.ordered_work prepared.1.1 hC H hH hHeight)
    (BinaryThreeFactoryMeasured.ordered_usage prepared.1.1 hC H hH hHeight)
  have hShift := BinaryNestedFirstAssemblyMeasured.shift_bounds child.1.1 mirror _ hP hQ hMirror
  have hResult := collect_bounds prepared child shifted _ _ _ _ _ _ hPrepared hChild hShift
  simp only [fromPrepared_record]
  simpa only [child,shifted] using hResult

theorem uniform_bounds (input : Input) (mirror : SignedWord) (hC : input.Canonical) (hM : CanonicalWord mirror)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hMH : RationalHeight (value mirror) s) :
    (uniform input mirror).2 ≤ workEnvelope s ∧ usage (uniform input mirror).1.2 ≤ envelope s := by
  let prepared := prepare input mirror
  have hState := (prepare_data input mirror).trans (BinaryNestedSecondUniformLifetime.inputWithTrace_erasure input mirror hC hM)
  have hPC : prepared.1.1.Canonical := by rw [hState]; exact BinaryNestedSecondUniformLifetime.preparedInput_canonical input mirror hC hM
  have hPH : BinaryOrderedThreeFactoryWork.InputHeight prepared.1.1 (expressionHeightBudget s 1) := by
    rw [hState]; exact BinaryNestedSecondUniformLifetime.preparedInput_height input mirror hC hM s hs hH hMH
  have hMW : width mirror ≤ shiftWidth (expressionHeightBudget s 1) := by
    have h := hM.2.trans (rationalWordWidth_of_height hMH)
    have hm := (expressionHeightBudget_ge_input s 1).trans (expressionHeightBudget_ge_input (expressionHeightBudget s 1) 18)
    unfold shiftWidth; omega
  have hResult := fromPrepared_bounds prepared mirror hPC _ (hs.trans (expressionHeightBudget_ge_input s 1)) hPH hMW _ _
    (prepare_bounds input mirror hC hM s hH hMH)
  simp only [uniform_record]
  unfold workEnvelope envelope
  with_reducible exact hResult

def selected (input : Input) (parameters : FixedArrayTable 9 SignedWord) := uniform input (parameters.read 6)

theorem selected_data (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    (selected input parameters).1.1 = (BinaryNestedSecondUniformLifetime.selectedWithTrace input parameters).1 := by
  unfold selected BinaryNestedSecondUniformLifetime.selectedWithTrace
  with_reducible exact uniform_data input (parameters.read 6)

theorem selected_bounds (input : Input) (parameters : FixedArrayTable 9 SignedWord) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    (selected input parameters).2 ≤ workEnvelope (expressionHeightBudget s 16) ∧
      usage (selected input parameters).1.2 ≤ envelope (expressionHeightBudget s 16) := by
  have hMirror : parameters.read 6 = BinaryNestedComponents.mirror input := by rw [hParameters]; rfl
  unfold selected
  rw [hMirror]
  have hResult := uniform_bounds input (BinaryNestedComponents.mirror input) hC (BinaryNestedComponents.mirror_canonical input hC)
    _ (hs.trans (expressionHeightBudget_ge_input s 16))
    (BinaryFactoryHeight.InputHeight.mono hH (expressionHeightBudget_ge_input s 16))
    (BinaryNestedRemainingFactoryWork.mirror_height input hC s hs hH)
  with_reducible exact hResult

theorem all_prefix (input : Input) (mirror : SignedWord) (hC : input.Canonical) (hM : CanonicalWord mirror)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hMH : RationalHeight (value mirror) s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (uniform input mirror).1.2 steps ≤ borrowed+envelope s ∧ framePeak ((uniform input mirror).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (uniform_bounds input mirror hC hM s hs hH hMH).2 borrowed steps

end Blotto.BinaryNestedSecondUniformMeasured
