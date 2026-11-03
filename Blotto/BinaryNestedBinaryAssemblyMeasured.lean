import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryNestedSecondUniformMeasured
import Blotto.BinaryNestedBinaryAssemblyLifetime

/-! One actual measured complement and eighteen measured products form a
nine-plus-nine binary mixture, with measured endpoint-reference packing. -/
namespace Blotto.BinaryNestedBinaryAssemblyMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryLifetimeUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 1200000

abbrev Small := BinaryStoredOverlapEnvironment.Segment 3 9
abbrev Large := BinaryStoredOverlapEnvironment.Segment 3 18

set_option cleanup.letToHave false in
def weightsWithExtras (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) : ((FixedArrayTable 18 SignedWord × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build 18 (fun slot => Fin.addCases (n := 9)
    (fun j => BinaryNormalizedCoordinate.opcode .mul p (first.read j))
    (fun j => BinaryNormalizedCoordinate.opcode .mul q (second.read j)) slot)

def weights (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) : (FixedArrayTable 18 SignedWord × Trace) × ℕ :=
  (weightsWithExtras p q first second).1

theorem weightsWithExtras_compat (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) :
    (weightsWithExtras p q first second).1 = weights p q first second := rfl

theorem weights_record (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) :
    weights p q first second =
  BinaryLifetimeArrayMeasured.build 18 (fun slot => Fin.addCases (n := 9)
    (fun j => BinaryPlannedQuadratic.apply .mul p (first.read j))
    (fun j => BinaryPlannedQuadratic.apply .mul q (second.read j)) slot) := by
  simp only [weights,weightsWithExtras,BinaryLifetimeArrayExtras.build_record]
  congr 1
  funext slot
  refine Fin.addCases (n := 9) (m := 9) (fun j => ?_) (fun j => ?_) slot <;>
    simp only [Fin.addCases_left,Fin.addCases_right,BinaryNormalizedCoordinate.opcode_record]

theorem weights_data (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) :
    (weights p q first second).1.1 = (BinaryNestedBinaryAssemblyLifetime.weightsWithTrace p q first second).1 := by
  apply BinaryOverlapInputPreparation.table_ext
  intro slot
  refine Fin.addCases (n := 9) (m := 9) (fun j => ?_) (fun j => ?_) slot <;>
    simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,weights_record,BinaryNestedBinaryAssemblyLifetime.weightsWithTrace,BinaryLifetimeArrayMeasured.build_data,
      BinaryLifetimeArray.build_erases,FixedArrayTable.read_ofFn,Fin.addCases_left,Fin.addCases_right,BinaryQuadraticMeasured.apply_erases]

def weightPrice (W : ℕ) : ℕ := 18*BinaryReflectedSystemMeasured.opcodePrice W+64*19^2
def weightEnvelope (W : ℕ) : ℕ := 19*opcodeEnvelope W+BinaryLifetimeArrayMeasured.storageReserve 18+46

theorem weights_bounds (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) (W : ℕ)
    (hp : width p ≤ W) (hq : width q ≤ W) (hf : ∀ j,width (first.read j) ≤ W) (hs : ∀ j,width (second.read j) ≤ W) :
    (weights p q first second).2 ≤ weightPrice W ∧ usage (weights p q first second).1.2 ≤ weightEnvelope W := by
  simp only [weights_record, BinaryPlannedQuadratic.apply_previous]
  let produce : Fin 18 → (SignedWord × Trace) × ℕ := fun slot => Fin.addCases (n := 9)
    (fun j => BinaryQuadraticMeasured.apply .mul p (first.read j))
    (fun j => BinaryQuadraticMeasured.apply .mul q (second.read j)) slot
  have hEach : ∀ slot,(produce slot).2 ≤ BinaryReflectedSystemMeasured.opcodePrice W ∧ usage (produce slot).1.2 ≤ opcodeEnvelope W := by
    intro slot
    refine Fin.addCases (n := 9) (m := 9) (fun j => ?_) (fun j => ?_) slot
    · simpa only [produce,Fin.addCases_left] using BinaryReflectedSystemMeasured.opcode_bounds .mul p (first.read j) W hp (hf j)
    · simpa only [produce,Fin.addCases_right] using BinaryReflectedSystemMeasured.opcode_bounds .mul q (second.read j) W hq (hs j)
  have hW := BinaryLifetimeArrayMeasured.build_work_bound 18 produce _ (fun slot => (hEach slot).1)
  have hU := BinaryLifetimeArrayMeasured.build_bounds 18 produce (opcodeEnvelope W) (opcodeEnvelope W)
    (by intro slot; have h := (hEach slot).2; unfold usage at h; omega)
    (by intro slot; have h := (hEach slot).2; unfold usage at h; omega)
  refine ⟨hW,?_⟩
  exact hU.trans_eq (by unfold weightEnvelope; omega)

def rows {α : Type*} (first second : FixedArrayTable 9 α) : (FixedArrayTable 18 α × Trace) × ℕ :=
  BinaryThreeReferenceMeasured.references 18 (Fin.addCases (n := 9) first.read second.read)

theorem rows_data {α : Type*} (first second : FixedArrayTable 9 α) :
    (rows first second).1.1 = (BinaryNestedBinaryAssemblyLifetime.rowsWithTrace first second).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,rows,BinaryThreeReferenceMeasured.references_data,BinaryNestedBinaryAssemblyLifetime.rowsWithTrace_erasure]

def collect (complement : (SignedWord × Trace) × ℕ) (weight : (FixedArrayTable 18 SignedWord × Trace) × ℕ)
    (P Q : (FixedArrayTable 18 (FixedArrayTable 3 SignedWord) × Trace) × ℕ) : (Large × Trace) × ℕ :=
  ((⟨weight.1.1,P.1.1,Q.1.1⟩,wrap 40 3 [complement.1.2,weight.1.2,P.1.2,Q.1.2]),complement.2+weight.2+P.2+Q.2+16)

set_option cleanup.letToHave false in
def fromComplementWithExtras (p : SignedWord) (first second : Small) (complement : (SignedWord × Trace) × ℕ) : ((Large × Trace) × ℕ) × ℕ :=
  let weight := weightsWithExtras p complement.1.1 first.weight second.weight
  (collect complement weight.1 (rows first.P second.P) (rows first.Q second.Q),weight.2)

def fromComplement (p : SignedWord) (first second : Small) (complement : (SignedWord × Trace) × ℕ) : (Large × Trace) × ℕ :=
  (fromComplementWithExtras p first second complement).1

theorem fromComplementWithExtras_compat (p : SignedWord) (first second : Small) (complement : (SignedWord × Trace) × ℕ) :
    (fromComplementWithExtras p first second complement).1 = fromComplement p first second complement := rfl

theorem fromComplement_record (p : SignedWord) (first second : Small) (complement : (SignedWord × Trace) × ℕ) :
    fromComplement p first second complement =
  collect complement (weights p complement.1.1 first.weight second.weight) (rows first.P second.P) (rows first.Q second.Q) := by
  simp only [fromComplement,fromComplementWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,weightsWithExtras_compat]

set_option cleanup.letToHave false in
def binaryWithExtras (p : SignedWord) (first second : Small) : ((Large × Trace) × ℕ) × ℕ :=
  let complement := BinaryNormalizedCoordinate.opcode .sub BinaryExpressionCompiler.Constant.one.word p
  let produced := fromComplementWithExtras p first second complement.1
  (produced.1,complement.2+produced.2)

def binary (p : SignedWord) (first second : Small) : (Large × Trace) × ℕ :=
  (binaryWithExtras p first second).1

theorem binaryWithExtras_compat (p : SignedWord) (first second : Small) :
    (binaryWithExtras p first second).1 = binary p first second := rfl

theorem binary_record (p : SignedWord) (first second : Small) :
    binary p first second =
  fromComplement p first second (BinaryPlannedQuadratic.apply .sub BinaryExpressionCompiler.Constant.one.word p) := by
  simp only [binary,binaryWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,weightsWithExtras_compat,fromComplementWithExtras_compat]

theorem binary_data (p : SignedWord) (first second : Small) :
    (binary p first second).1.1 = (BinaryNestedBinaryAssemblyLifetime.binaryWithTrace p first second).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,binary_record,fromComplement_record,collect,BinaryNestedBinaryAssemblyLifetime.binaryWithTrace,
    weights_data,rows_data,BinaryQuadraticMeasured.apply_erases]

def workEnvelope (W : ℕ) : ℕ := BinaryReflectedSystemMeasured.opcodePrice (3*W+1)+weightPrice (3*W+1)+2*23176+16

def envelope (W : ℕ) : ℕ := opcodeEnvelope (3*W+1)+weightEnvelope (3*W+1)+2*11807+128

theorem collect_bounds (complement : (SignedWord × Trace) × ℕ) (weight : (FixedArrayTable 18 SignedWord × Trace) × ℕ)
    (P Q : (FixedArrayTable 18 (FixedArrayTable 3 SignedWord) × Trace) × ℕ) (C W R B U F : ℕ)
    (hc : complement.2 ≤ C ∧ usage complement.1.2 ≤ B) (hw : weight.2 ≤ W ∧ usage weight.1.2 ≤ U)
    (hp : P.2 ≤ R ∧ usage P.1.2 ≤ F) (hq : Q.2 ≤ R ∧ usage Q.1.2 ≤ F) :
    (collect complement weight P Q).2 ≤ C+W+2*R+16 ∧ usage (collect complement weight P Q).1.2 ≤ B+U+2*F+128 := by
  have ht := wrap_usage 40 3 [complement.1.2,weight.1.2,P.1.2,Q.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at ht
  change complement.2+weight.2+P.2+Q.2+16 ≤ _ ∧ usage (wrap 40 3 [complement.1.2,weight.1.2,P.1.2,Q.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem fromComplement_bounds (p : SignedWord) (first second : Small) (complement : (SignedWord × Trace) × ℕ)
    (W : ℕ) (hp : width p ≤ W) (hc : width complement.1.1 ≤ W)
    (hf : ∀ j,width (first.weight.read j) ≤ W) (hs : ∀ j,width (second.weight.read j) ≤ W)
    (C U : ℕ) (hComplement : complement.2 ≤ C ∧ usage complement.1.2 ≤ U) :
    (fromComplement p first second complement).2 ≤ C+weightPrice W+2*23176+16 ∧
    usage (fromComplement p first second complement).1.2 ≤ U+weightEnvelope W+2*11807+128 := by
  have hP : (rows first.P second.P).2 ≤ 23176 ∧ usage (rows first.P second.P).1.2 ≤ 11807 :=
    ⟨BinaryThreeReferenceMeasured.references_work 18 _,BinaryThreeReferenceMeasured.references_usage 18 _⟩
  have hQ : (rows first.Q second.Q).2 ≤ 23176 ∧ usage (rows first.Q second.Q).1.2 ≤ 11807 :=
    ⟨BinaryThreeReferenceMeasured.references_work 18 _,BinaryThreeReferenceMeasured.references_usage 18 _⟩
  exact collect_bounds complement _ _ _ _ _ _ _ _ _ hComplement (weights_bounds p complement.1.1 first.weight second.weight W hp hc hf hs) hP hQ

theorem binary_bounds (p : SignedWord) (first second : Small) (hP : CanonicalWord p) (W : ℕ) (hW : 1 ≤ W)
    (hp : width p ≤ W) (hf : ∀ j,width (first.weight.read j) ≤ W) (hs : ∀ j,width (second.weight.read j) ≤ W) :
    (binary p first second).2 ≤ workEnvelope W ∧ usage (binary p first second).1.2 ≤ envelope W := by
  let complement := BinaryQuadraticMeasured.apply .sub BinaryExpressionCompiler.Constant.one.word p
  have hOne : width BinaryExpressionCompiler.Constant.one.word ≤ W := hW
  have hCW : width complement.1.1 ≤ 3*W+1 := by
    rw [BinaryQuadraticMeasured.apply_erases,BinaryQuadraticLifetime.applyWithTrace_state .sub _ _
      (BinaryExpressionCompiler.Constant.word_canonical .one).1 hP.1]
    have h := BinaryPRGPreparationWork.apply_stored_width .sub BinaryExpressionCompiler.Constant.one.word p
    have hm : BinaryRationalArithmetic.pairWidth BinaryExpressionCompiler.Constant.one.word p ≤ W := max_le hOne hp
    omega
  have hComplement := BinaryReflectedSystemMeasured.opcode_bounds .sub BinaryExpressionCompiler.Constant.one.word p (3*W+1) (by omega) (by omega)
  have hResult := fromComplement_bounds p first second complement (3*W+1) (by omega) hCW
    (fun j => (hf j).trans (by omega)) (fun j => (hs j).trans (by omega)) _ _ hComplement
  simp only [binary_record, BinaryPlannedQuadratic.apply_previous]
  exact hResult

theorem all_prefix (p : SignedWord) (first second : Small) (hP : CanonicalWord p) (W : ℕ) (hW : 1 ≤ W)
    (hp : width p ≤ W) (hf : ∀ j,width (first.weight.read j) ≤ W) (hs : ∀ j,width (second.weight.read j) ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (binary p first second).1.2 steps ≤ borrowed+envelope W ∧ framePeak ((binary p first second).1.2.take steps) ≤ envelope W :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (binary_bounds p first second hP W hW hp hf hs).2 borrowed steps

end Blotto.BinaryNestedBinaryAssemblyMeasured
