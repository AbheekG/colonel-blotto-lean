import Blotto.BinaryNestedFirstAssemblyMeasured
import Blotto.BinaryNestedParameterMeasured
import Blotto.BinaryNestedOrderMeasured
import Blotto.BinaryQuadraticThreeFactoryMeasured
import Blotto.BinaryNestedFirstDescriptorLifetime

/-! One measured conditional parameter table and guard select the actual
measured regular geometry/factory/translation or the measured corner. Original
input/location heights derive source work and enlarged retained bounds. -/
namespace Blotto.BinaryNestedFirstDescriptorMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 9

def joinPositive (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ)
    (table shifted : (Segment × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  ((shifted.1.1,wrap 40 3 [geometry.1.2,table.1.2,shifted.1.2]),geometry.2+table.2+shifted.2+12)

set_option cleanup.letToHave false in
def positiveFromWithExtras (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (x : SignedWord) : ((Segment × Trace) × ℕ) × ℕ :=
  let table := BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras geometry.1.1
  let shifted := BinaryNestedFirstAssemblyMeasured.shiftWithExtras table.1.1.1 x
  (joinPositive geometry table.1 shifted.1,table.2+shifted.2)

def positiveFrom (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (x : SignedWord) : (Segment × Trace) × ℕ :=
  (positiveFromWithExtras geometry x).1

theorem positiveFromWithExtras_compat (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (x : SignedWord) :
    (positiveFromWithExtras geometry x).1 = positiveFrom geometry x := rfl

theorem positiveFrom_record (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (x : SignedWord) :
    positiveFrom geometry x =
  let table := BinaryQuadraticThreeFactoryMeasured.descriptor geometry.1.1
  let shifted := BinaryNestedFirstAssemblyMeasured.shift table.1.1 x
  joinPositive geometry table shifted := by
  simp only [positiveFrom,positiveFromWithExtras,BinaryQuadraticThreeFactoryMeasured.vertexRowWithExtras_compat,BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras_compat,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedFirstAssemblyMeasured.rowShiftWithExtras_compat,BinaryNestedFirstAssemblyMeasured.rowsShiftWithExtras_compat,BinaryNestedFirstAssemblyMeasured.shiftWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat]
  try { split_ifs <;> rfl }

set_option cleanup.letToHave false in
def positiveWithExtras (input : Input) (x : SignedWord) : ((Segment × Trace) × ℕ) × ℕ :=
  let geometry := BinaryNestedParameterMeasured.geometryWithExtras input x
  let produced := positiveFromWithExtras geometry.1 x
  (produced.1,geometry.2+produced.2)

def positive (input : Input) (x : SignedWord) : (Segment × Trace) × ℕ :=
  (positiveWithExtras input x).1

theorem positiveWithExtras_compat (input : Input) (x : SignedWord) :
    (positiveWithExtras input x).1 = positive input x := rfl

theorem positive_record (input : Input) (x : SignedWord) :
    positive input x =
  positiveFrom (BinaryNestedParameterMeasured.geometry input x) x := by
  simp only [positive,positiveWithExtras,BinaryQuadraticThreeFactoryMeasured.vertexRowWithExtras_compat,BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras_compat,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedFirstAssemblyMeasured.rowShiftWithExtras_compat,BinaryNestedFirstAssemblyMeasured.rowsShiftWithExtras_compat,BinaryNestedFirstAssemblyMeasured.shiftWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,positiveFromWithExtras_compat]
  try { split_ifs <;> rfl }

theorem positive_data (input : Input) (x : SignedWord) :
    (positive input x).1.1 = (BinaryNestedFirstAssemblyLifetime.shiftThirdWithTrace
      (BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace (BinaryNestedParameterAtLifetime.geometryWithTrace input x).1).1 x).1 := by
  simp only [positive_record,positiveFrom_record,joinPositive,BinaryNestedFirstAssemblyMeasured.shift_data,
    BinaryQuadraticThreeFactoryMeasured.descriptor_data,BinaryNestedParameterMeasured.geometry_data]

def shiftWidth (H : ℕ) : ℕ := 2*expressionHeightBudget H 16+1

def positivePrice (s : ℕ) : ℕ := BinaryNestedParameterMeasured.workEnvelope 4 s+
  BinaryQuadraticThreeFactoryMeasured.workEnvelope (expressionHeightBudget s 16)+
  BinaryNestedFirstAssemblyMeasured.shiftPrice (shiftWidth (expressionHeightBudget s 16))+12

def positiveEnvelope (s : ℕ) : ℕ := BinaryNestedParameterMeasured.envelope 4 s 96 8+
  BinaryQuadraticThreeFactoryMeasured.envelope (expressionHeightBudget s 16)+
  BinaryNestedFirstAssemblyMeasured.shiftEnvelope (shiftWidth (expressionHeightBudget s 16))+64

theorem joinPositive_bounds (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ)
    (table shifted : (Segment × Trace) × ℕ) (G T S B F H : ℕ)
    (hg : geometry.2 ≤ G ∧ usage geometry.1.2 ≤ B) (ht : table.2 ≤ T ∧ usage table.1.2 ≤ F)
    (hs : shifted.2 ≤ S ∧ usage shifted.1.2 ≤ H) :
    (joinPositive geometry table shifted).2 ≤ G+T+S+12 ∧ usage (joinPositive geometry table shifted).1.2 ≤ B+F+H+64 := by
  have hw := wrap_usage 40 3 [geometry.1.2,table.1.2,shifted.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change geometry.2+table.2+shifted.2+12 ≤ _ ∧ usage (wrap 40 3 [geometry.1.2,table.1.2,shifted.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem positiveFrom_bounds (geometry : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (x : SignedWord)
    (hC : ∀ j,CanonicalWord (geometry.1.1.read j)) (H : ℕ) (hH : 3 ≤ H)
    (hHeight : BinarySyntaxUniformWork.EnvHeight geometry.1.1 H) (hX : width x ≤ shiftWidth H)
    (G U : ℕ) (hGeometry : geometry.2 ≤ G ∧ usage geometry.1.2 ≤ U) :
    (positiveFrom geometry x).2 ≤ G+BinaryQuadraticThreeFactoryMeasured.workEnvelope H+
      BinaryNestedFirstAssemblyMeasured.shiftPrice (shiftWidth H)+12 ∧
    usage (positiveFrom geometry x).1.2 ≤ U+BinaryQuadraticThreeFactoryMeasured.envelope H+
      BinaryNestedFirstAssemblyMeasured.shiftEnvelope (shiftWidth H)+64 := by
  let table := BinaryQuadraticThreeFactoryMeasured.descriptor geometry.1.1
  let shifted := BinaryNestedFirstAssemblyMeasured.shift table.1.1 x
  have hTableState := (BinaryQuadraticThreeFactoryMeasured.descriptor_data geometry.1.1).trans
    (BinaryQuadraticThreeFactoryLifetime.descriptorWithTrace_erases geometry.1.1 hC)
  have hTableC : table.1.1.Canonical := by
    rw [hTableState]
    exact BinaryThreeDescriptorCompiler.descriptor_canonical _ hC
  have hTableH : BinaryFactoryHeight.SegmentHeight table.1.1 (expressionHeightBudget H 16) := by
    rw [hTableState]
    exact BinaryThreeFactoryWork.descriptor_height geometry.1.1 hC H hH hHeight
  have hP : ∀ slot,width ((table.1.1.P.read slot).read 2) ≤ shiftWidth H := by
    intro slot
    have h := (hTableC.2.1 slot 2).2.trans (rationalWordWidth_of_height (hTableH.2 slot 2).1)
    unfold shiftWidth; omega
  have hQ : ∀ slot,width ((table.1.1.Q.read slot).read 2) ≤ shiftWidth H := by
    intro slot
    have h := (hTableC.2.2 slot 2).2.trans (rationalWordWidth_of_height (hTableH.2 slot 2).2)
    unfold shiftWidth; omega
  have hTable := And.intro (BinaryQuadraticThreeFactoryMeasured.descriptor_work geometry.1.1 hC H hH hHeight)
    (BinaryQuadraticThreeFactoryMeasured.descriptor_usage geometry.1.1 hC H hH hHeight)
  have hShift := BinaryNestedFirstAssemblyMeasured.shift_bounds table.1.1 x _ hP hQ hX
  have hResult := joinPositive_bounds geometry table shifted _ _ _ _ _ _ hGeometry hTable hShift
  simp only [positiveFrom_record]
  simpa only [table,shifted] using hResult

theorem positive_bounds (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s) :
    (positive input x).2 ≤ positivePrice s ∧ usage (positive input x).1.2 ≤ positiveEnvelope s := by
  let geometry := BinaryNestedParameterMeasured.geometry input x
  have hGeometry := BinaryNestedParameterMeasured.geometry_bounds input x hC hX s hs hH hXH
  have hState := (BinaryNestedParameterMeasured.geometry_data input x).trans
    (BinaryNestedParameterAtLifetime.geometryWithTrace_erasure input x hC hX)
  have hGC : ∀ j,CanonicalWord (geometry.1.1.read j) := by rw [hState]; exact BinaryNestedParameters.geometry_canonical input x hC hX
  have hGH : BinarySyntaxUniformWork.EnvHeight geometry.1.1 (expressionHeightBudget s 16) := by
    intro j; rw [hState]; exact BinaryNestedParameterWork.geometry_height input x hC hX s hs hH hXH j
  have hXW : width x ≤ shiftWidth (expressionHeightBudget s 16) := by
    have h := hX.2.trans (rationalWordWidth_of_height hXH)
    have hm := (expressionHeightBudget_ge_input s 16).trans (expressionHeightBudget_ge_input (expressionHeightBudget s 16) 16)
    unfold shiftWidth; omega
  have hResult := positiveFrom_bounds geometry x hGC _ (hs.trans (expressionHeightBudget_ge_input s 16)) hGH hXW _ _ hGeometry
  simp only [positive_record]
  simpa only [geometry,positivePrice,positiveEnvelope] using hResult

def finish (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) (guard : (Bool × Trace) × ℕ)
    (regular corner : Unit → (Segment × Trace) × ℕ) : (Segment × Trace) × ℕ :=
  let chosen := if !guard.1.1 then regular () else corner ()
  ((chosen.1.1,wrap 40 3 [parameters.1.2,guard.1.2,chosen.1.2]),parameters.2+guard.2+chosen.2+12)

set_option cleanup.letToHave false in
def fromParametersWithExtras (input : Input) (x : SignedWord) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) : ((Segment × Trace) × ℕ) × ℕ :=
  let guard := BinaryQuadraticExpressionMeasured.compare (parameters.1.1.read 4) BinaryRationalOpcode.zero
  let chosen := if !guard.1.1 then positiveWithExtras input x else (BinaryNestedFirstAssemblyMeasured.corner input x,0)
  (((chosen.1.1.1,wrap 40 3 [parameters.1.2,guard.1.2,chosen.1.1.2]),parameters.2+guard.2+chosen.1.2+12),chosen.2)

def fromParameters (input : Input) (x : SignedWord) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) :
    (Segment × Trace) × ℕ :=
  (fromParametersWithExtras input x parameters).1

theorem fromParametersWithExtras_compat (input : Input) (x : SignedWord) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) :
    (fromParametersWithExtras input x parameters).1 = fromParameters input x parameters := rfl

theorem fromParameters_record (input : Input) (x : SignedWord) (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) :
    fromParameters input x parameters =
  let guard := BinaryQuadraticExpressionMeasured.compare (parameters.1.1.read 4) BinaryRationalOpcode.zero
  finish parameters guard (fun _ => positive input x) (fun _ => BinaryNestedFirstAssemblyMeasured.corner input x) := by
  simp only [fromParameters,fromParametersWithExtras,finish,BinaryQuadraticThreeFactoryMeasured.vertexRowWithExtras_compat,BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras_compat,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedFirstAssemblyMeasured.rowShiftWithExtras_compat,BinaryNestedFirstAssemblyMeasured.rowsShiftWithExtras_compat,BinaryNestedFirstAssemblyMeasured.shiftWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,positiveFromWithExtras_compat,positiveWithExtras_compat]
  try { split_ifs <;> rfl }

set_option cleanup.letToHave false in
def descriptorWithExtras (input : Input) (x : SignedWord) : ((Segment × Trace) × ℕ) × ℕ :=
  let parameters := BinaryNestedParameterMeasured.prepareAtWithExtras input x
  let produced := fromParametersWithExtras input x parameters.1
  (produced.1,parameters.2+produced.2)

def descriptor (input : Input) (x : SignedWord) : (Segment × Trace) × ℕ :=
  (descriptorWithExtras input x).1

theorem descriptorWithExtras_compat (input : Input) (x : SignedWord) :
    (descriptorWithExtras input x).1 = descriptor input x := rfl

theorem descriptor_record (input : Input) (x : SignedWord) :
    descriptor input x =
  fromParameters input x (BinaryNestedParameterMeasured.prepareAt input x) := by
  simp only [descriptor,descriptorWithExtras,BinaryQuadraticThreeFactoryMeasured.vertexRowWithExtras_compat,BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras_compat,BinaryNestedParameterMeasured.runProgramsWithExtras_compat,BinaryNestedParameterMeasured.prepareAtWithExtras_compat,BinaryNestedParameterMeasured.prepareWithExtras_compat,BinaryNestedParameterMeasured.geometryWithExtras_compat,BinaryNestedFirstAssemblyMeasured.rowShiftWithExtras_compat,BinaryNestedFirstAssemblyMeasured.rowsShiftWithExtras_compat,BinaryNestedFirstAssemblyMeasured.shiftWithExtras_compat,BinaryNestedOrderMeasured.orderWithExtras_compat,positiveFromWithExtras_compat,positiveWithExtras_compat,fromParametersWithExtras_compat]
  try { split_ifs <;> rfl }

theorem descriptor_data (input : Input) (x : SignedWord) :
    (descriptor input x).1.1 = (BinaryNestedFirstDescriptorLifetime.descriptorWithTrace input x).1 := by
  simp only [descriptor_record,fromParameters_record,finish,BinaryNestedFirstDescriptorLifetime.descriptorWithTrace,
    BinaryNestedParameterMeasured.prepareAt_data,BinaryQuadraticExpressionMeasured.compare_erases]
  split_ifs <;> simp only [positive_data,BinaryNestedFirstAssemblyMeasured.corner_data]

def workEnvelope (s : ℕ) : ℕ := BinaryNestedParameterMeasured.workEnvelope 9 s+
  BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s 16)+positivePrice s+50000+12

def envelope (s : ℕ) : ℕ := BinaryNestedParameterMeasured.envelope 9 s 128 10+
  BinaryThreeGeometryLifetime.comparisonEnvelope (2*expressionHeightBudget s 16+1)+positiveEnvelope s+50000+96

theorem finish_bounds (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ) (guard : (Bool × Trace) × ℕ)
    (regular corner : Unit → (Segment × Trace) × ℕ) (P G T C B H U F : ℕ)
    (hp : parameters.2 ≤ P ∧ usage parameters.1.2 ≤ B) (hg : guard.2 ≤ G ∧ usage guard.1.2 ≤ H)
    (ht : (regular ()).2 ≤ T ∧ usage (regular ()).1.2 ≤ U) (hc : (corner ()).2 ≤ C ∧ usage (corner ()).1.2 ≤ F) :
    (finish parameters guard regular corner).2 ≤ P+G+T+C+12 ∧
      usage (finish parameters guard regular corner).1.2 ≤ B+H+U+F+96 := by
  unfold finish
  dsimp only
  split
  · have hw := wrap_usage 40 3 [parameters.1.2,guard.1.2,(regular ()).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change parameters.2+guard.2+(regular ()).2+12 ≤ _ ∧ usage (wrap 40 3 [parameters.1.2,guard.1.2,(regular ()).1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · have hw := wrap_usage 40 3 [parameters.1.2,guard.1.2,(corner ()).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change parameters.2+guard.2+(corner ()).2+12 ≤ _ ∧ usage (wrap 40 3 [parameters.1.2,guard.1.2,(corner ()).1.2]) ≤ _
    exact ⟨by omega,by omega⟩

theorem fromParameters_bounds (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s)
    (parameters : (FixedArrayTable 9 SignedWord × Trace) × ℕ)
    (hPC : CanonicalWord (parameters.1.1.read 4))
    (hPH : RationalHeight (value (parameters.1.1.read 4)) (expressionHeightBudget s 16))
    (hP : parameters.2 ≤ BinaryNestedParameterMeasured.workEnvelope 9 s ∧
      usage parameters.1.2 ≤ BinaryNestedParameterMeasured.envelope 9 s 128 10) :
    (fromParameters input x parameters).2 ≤ workEnvelope s ∧ usage (fromParameters input x parameters).1.2 ≤ envelope s := by
  let guard := BinaryQuadraticExpressionMeasured.compare (parameters.1.1.read 4) BinaryRationalOpcode.zero
  have hZeroC : CanonicalWord BinaryRationalOpcode.zero := ⟨BinaryRationalOpcode.zero_valid,by decide⟩
  have hG := BinaryNestedOrderMeasured.compare_bounds (parameters.1.1.read 4) BinaryRationalOpcode.zero hPC hZeroC _ hPH
    (BinaryFactoryHeight.zero_height _ (hs.trans (expressionHeightBudget_ge_input s 16)))
  have hT := positive_bounds input x hC hX s hs hH hXH
  have hCnr := BinaryNestedFirstAssemblyMeasured.corner_bounds input x
  have hResult := finish_bounds parameters guard (fun _ => positive input x) (fun _ => BinaryNestedFirstAssemblyMeasured.corner input x)
    _ _ _ _ _ _ _ _ hP hG hT hCnr
  simp only [fromParameters_record]
  simpa only [guard,workEnvelope,envelope] using hResult

theorem descriptor_bounds (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s) :
    (descriptor input x).2 ≤ workEnvelope s ∧ usage (descriptor input x).1.2 ≤ envelope s := by
  let parameters := BinaryNestedParameterMeasured.prepareAt input x
  have hP := BinaryNestedParameterMeasured.prepareAt_bounds input x hC hX s hs hH hXH
  have hState := (BinaryNestedParameterMeasured.prepareAt_data input x).trans
    (BinaryNestedParameterAtLifetime.prepareWithTrace_erasure input x hC hX)
  have hPC : CanonicalWord (parameters.1.1.read 4) := by rw [hState]; exact BinaryNestedParameters.prepare_canonical input x hC hX 4
  have hPH : RationalHeight (value (parameters.1.1.read 4)) (expressionHeightBudget s 16) := by
    rw [hState]; exact BinaryNestedParameterWork.prepare_height input x hC hX s hs hH hXH 4
  have hResult := fromParameters_bounds input x hC hX s hs hH hXH parameters hPC hPH hP
  simp only [descriptor_record]
  with_reducible exact hResult

theorem all_prefix (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptor input x).1.2 steps ≤ borrowed+envelope s ∧ framePeak ((descriptor input x).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptor_bounds input x hC hX s hs hH hXH).2 borrowed steps

end Blotto.BinaryNestedFirstDescriptorMeasured
