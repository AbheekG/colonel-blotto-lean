import Blotto.BinaryNestedOrderMeasured
import Blotto.BinaryThreeFactoryMeasured

/-! Reached measured q-boundary guards feed complete measured three-variable
factories and actual eighteen-slot packing. Interior inputs return none without
running either factory. Original nested fields derive all source bounds. -/
namespace Blotto.BinaryNestedBoundaryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 700000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def childFrom (table : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  let padded := BinaryNestedReferenceMeasured.pad table.1.1
  ((padded.1.1,wrap 32 2 [table.1.2,padded.1.2]),table.2+padded.2+8)

set_option cleanup.letToHave false in
def childWithExtras (input : BinaryThreeInputCompiler.Input) : ((Segment × Trace) × ℕ) × ℕ :=
  let table := BinaryThreeFactoryMeasured.descriptorWithExtras input
  (childFrom table.1,table.2)

def child (input : BinaryThreeInputCompiler.Input) : (Segment × Trace) × ℕ :=
  (childWithExtras input).1

theorem childWithExtras_compat (input : BinaryThreeInputCompiler.Input) :
    (childWithExtras input).1 = child input := rfl

theorem child_record (input : BinaryThreeInputCompiler.Input) :
    child input =
  childFrom (BinaryThreeFactoryMeasured.descriptor input) := by
  simp only [child,childWithExtras,BinaryNestedOrderMeasured.orderWithExtras_compat,BinaryThreeFactoryMeasured.orderedWithExtras_compat,BinaryThreeFactoryMeasured.descriptorWithExtras_compat]
  try { split_ifs <;> rfl }

theorem child_data (input : BinaryThreeInputCompiler.Input) :
    (child input).1.1 = (BinaryNestedBoundaryLifetime.padWithTrace (BinaryUnorderedThreeLifetime.descriptorWithTrace input).1).1 := by
  simp only [child_record,childFrom,BinaryNestedReferenceMeasured.pad_data,BinaryThreeFactoryMeasured.descriptor_data]

def childPrice (s : ℕ) : ℕ := BinaryThreeFactoryMeasured.workEnvelope s+70000+8
def childEnvelope (s : ℕ) : ℕ := BinaryThreeFactoryMeasured.envelope s+36000+64

theorem childFrom_bounds (table : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ) (T U : ℕ)
    (h : table.2 ≤ T ∧ usage table.1.2 ≤ U) :
    (childFrom table).2 ≤ T+70000+8 ∧ usage (childFrom table).1.2 ≤ U+36000+64 := by
  have hp := BinaryNestedReferenceMeasured.pad_bounds table.1.1
  have hw := wrap_usage 32 2 [table.1.2,(BinaryNestedReferenceMeasured.pad table.1.1).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change table.2+(BinaryNestedReferenceMeasured.pad table.1.1).2+8 ≤ _ ∧ usage (wrap 32 2 [table.1.2,_]) ≤ _
  exact ⟨by omega,by omega⟩

theorem child_bounds (input : BinaryThreeInputCompiler.Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    (child input).2 ≤ childPrice s ∧ usage (child input).1.2 ≤ childEnvelope s :=
  childFrom_bounds _ _ _ (BinaryThreeFactoryMeasured.descriptor_bounds input hC s hs hH)

def choose (zero : (Bool × Trace) × ℕ) (one : Unit → (Bool × Trace) × ℕ)
    (long short : Unit → (Segment × Trace) × ℕ) : (Option Segment × Trace) × ℕ :=
  if zero.1.1 then
    let table := long ()
    ((some table.1.1,wrap 32 2 [zero.1.2,table.1.2]),zero.2+table.2+8)
  else
    let next := one ()
    if next.1.1 then
      let table := short ()
      ((some table.1.1,wrap 32 2 [zero.1.2,next.1.2,table.1.2]),zero.2+next.2+table.2+12)
    else ((none,wrap 32 2 [zero.1.2,next.1.2]),zero.2+next.2+8)

set_option cleanup.letToHave false in
def boundaryWithExtras (input : Input) : ((Option Segment × Trace) × ℕ) × ℕ :=
  let zero := BinaryQuadraticExpressionMeasured.compare input.q BinaryRationalOpcode.zero
  if zero.1.1 then
    let table := childWithExtras (BinaryNestedSpecProfile.longInput input)
    (((some table.1.1.1,wrap 32 2 [zero.1.2,table.1.1.2]),zero.2+table.1.2+8),table.2)
  else
    let next := BinaryQuadraticExpressionMeasured.compare BinaryExpressionCompiler.Constant.one.word input.q
    if next.1.1 then
      let table := childWithExtras (BinaryNestedSpecProfile.shortInput input)
      (((some table.1.1.1,wrap 32 2 [zero.1.2,next.1.2,table.1.1.2]),zero.2+next.2+table.1.2+12),table.2)
    else (((none,wrap 32 2 [zero.1.2,next.1.2]),zero.2+next.2+8),0)

def boundary (input : Input) : (Option Segment × Trace) × ℕ :=
  (boundaryWithExtras input).1

theorem boundaryWithExtras_compat (input : Input) :
    (boundaryWithExtras input).1 = boundary input := rfl

theorem boundary_record (input : Input) :
    boundary input =
  choose (BinaryQuadraticExpressionMeasured.compare input.q BinaryRationalOpcode.zero)
    (fun _ => BinaryQuadraticExpressionMeasured.compare BinaryExpressionCompiler.Constant.one.word input.q)
    (fun _ => child (BinaryNestedSpecProfile.longInput input)) (fun _ => child (BinaryNestedSpecProfile.shortInput input)) := by
  simp only [boundary,boundaryWithExtras,choose]
  split_ifs <;> simp only [childWithExtras_compat]

theorem boundary_data (input : Input) :
    (boundary input).1.1 = (BinaryNestedBoundaryLifetime.boundaryWithTrace input).1 := by
  simp only [boundary_record,choose,BinaryNestedBoundaryLifetime.boundaryWithTrace,
    BinaryQuadraticExpressionMeasured.compare_erases,child_data]
  split_ifs <;> rfl

def workEnvelope (s : ℕ) : ℕ := 2*BinaryQuadraticExpression.uniformPrice s+childPrice s+16

def envelope (s : ℕ) : ℕ := 2*BinaryThreeGeometryLifetime.comparisonEnvelope (2*s+1)+childEnvelope s+128

theorem choose_bounds (zero : (Bool × Trace) × ℕ) (one : Unit → (Bool × Trace) × ℕ)
    (long short : Unit → (Segment × Trace) × ℕ) (C T U H : ℕ)
    (hz : zero.2 ≤ C ∧ usage zero.1.2 ≤ U) (ho : (one ()).2 ≤ C ∧ usage (one ()).1.2 ≤ U)
    (hl : (long ()).2 ≤ T ∧ usage (long ()).1.2 ≤ H) (hs : (short ()).2 ≤ T ∧ usage (short ()).1.2 ≤ H) :
    (choose zero one long short).2 ≤ 2*C+T+16 ∧ usage (choose zero one long short).1.2 ≤ 2*U+H+128 := by
  unfold choose
  split
  · have hw := wrap_usage 32 2 [zero.1.2,(long ()).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change zero.2+(long ()).2+8 ≤ _ ∧ usage (wrap 32 2 [zero.1.2,(long ()).1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · dsimp only
    split
    · have hw := wrap_usage 32 2 [zero.1.2,(one ()).1.2,(short ()).1.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change zero.2+(one ()).2+(short ()).2+12 ≤ _ ∧ usage (wrap 32 2 [zero.1.2,(one ()).1.2,(short ()).1.2]) ≤ _
      exact ⟨by omega,by omega⟩
    · have hw := wrap_usage 32 2 [zero.1.2,(one ()).1.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change zero.2+(one ()).2+8 ≤ _ ∧ usage (wrap 32 2 [zero.1.2,(one ()).1.2]) ≤ _
      exact ⟨by omega,by omega⟩

theorem boundary_bounds (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (boundary input).2 ≤ workEnvelope s ∧ usage (boundary input).1.2 ≤ envelope s := by
  have hZeroC : CanonicalWord BinaryRationalOpcode.zero := ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  have hz := BinaryNestedOrderMeasured.compare_bounds input.q BinaryRationalOpcode.zero hC.2.2.2.2.2 hZeroC s hH.2.2.2.2.2 (BinaryFactoryHeight.zero_height s hs)
  have ho := BinaryNestedOrderMeasured.compare_bounds BinaryExpressionCompiler.Constant.one.word input.q
    (BinaryExpressionCompiler.Constant.word_canonical .one) hC.2.2.2.2.2 s (BinaryFactoryHeight.one_height s hs) hH.2.2.2.2.2
  have hl := child_bounds (BinaryNestedSpecProfile.longInput input) (BinaryNestedSpecProfile.longInput_canonical input hC)
    s hs (BinaryNestedSpecFactoryWork.longInput_height input s hs hH)
  have ht := child_bounds (BinaryNestedSpecProfile.shortInput input) (BinaryNestedSpecProfile.shortInput_canonical input hC)
    s hs (BinaryNestedSpecFactoryWork.shortInput_height input s hs hH)
  simp only [boundary_record]
  unfold workEnvelope envelope
  exact choose_bounds _ _ _ _ _ _ _ _ hz ho hl ht

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (boundary input).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((boundary input).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (boundary_bounds input hC s hs hH).2 borrowed steps

end Blotto.BinaryNestedBoundaryMeasured
