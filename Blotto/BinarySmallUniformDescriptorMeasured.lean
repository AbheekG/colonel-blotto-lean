import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinarySmallUniformPreparationMeasured
import Blotto.BinaryThreeFactoryMeasured
import Blotto.BinarySmallUniformDescriptorLifetime

/-! The actual merged measured child feeds the measured three-variable factory.
All eighteen measured endpoint splits feed pinned returned arrays. The enlarged
trace and work have original prepared-field bounds; native model costs remain. -/
namespace Blotto.BinarySmallUniformDescriptorMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight BinaryLifetimeUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 500000

set_option cleanup.letToHave false in
def childWithExtras (input : BinarySmallUniformCompiler.Input) : ((BinaryThreeInputCompiler.Input × Trace) × ℕ) × ℕ :=
  let total := BinaryNormalizedCoordinate.opcode .add input.l0 input.l1
  (((⟨input.B,total.1.1.1,input.l2,input.l3,BinaryExpressionCompiler.Constant.one.word⟩,
    wrap 16 2 [total.1.1.2]),total.1.2+8),total.2)

def child (input : BinarySmallUniformCompiler.Input) : (BinaryThreeInputCompiler.Input × Trace) × ℕ :=
  (childWithExtras input).1

theorem childWithExtras_compat (input : BinarySmallUniformCompiler.Input) :
    (childWithExtras input).1 = child input := rfl

theorem child_record (input : BinarySmallUniformCompiler.Input) :
    child input =
  let total := BinaryPlannedQuadratic.apply .add input.l0 input.l1
  ((⟨input.B,total.1.1,input.l2,input.l3,BinaryExpressionCompiler.Constant.one.word⟩,
    wrap 16 2 [total.1.2]),total.2+8) := by
  simp only [child,childWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record]

theorem child_data (input : BinarySmallUniformCompiler.Input) :
    (child input).1.1 = (BinarySmallUniformDescriptorLifetime.childWithTrace input).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,child_record,BinarySmallUniformDescriptorLifetime.childWithTrace,BinaryQuadraticMeasured.apply_erases]

def childPrice (s : ℕ) : ℕ := BinarySmallUniformSplitMeasured.opcodePrice s+8
def childEnvelope (s : ℕ) : ℕ := opcodeEnvelope (2*s+1)+24

theorem child_bounds (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hH : BinarySmallUniformFactoryWork.InputHeight input s) :
    (child input).2 ≤ childPrice s ∧ usage (child input).1.2 ≤ childEnvelope s := by
  have hOp := BinarySmallUniformPreparationMeasured.opcode_bounds .add input.l0 input.l1 hC.2.1 hC.2.2.1 s hH.2.1 hH.2.2.1
  have hw := wrap_usage 16 2 [(BinaryQuadraticMeasured.apply .add input.l0 input.l1).1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  simp only [child_record, BinaryPlannedQuadratic.apply_previous]
  change (BinaryQuadraticMeasured.apply .add input.l0 input.l1).2+8 ≤ _ ∧ usage (wrap 16 2 [_]) ≤ _
  unfold childPrice childEnvelope
  exact ⟨by omega,by omega⟩

def assemble (merged : (BinaryThreeInputCompiler.Input × Trace) × ℕ)
    (table : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ)
    (P Q : (FixedArrayTable 9 (FixedArrayTable 4 SignedWord) × Trace) × ℕ) :
    (BinaryStoredOverlapEnvironment.Segment 4 9 × Trace) × ℕ :=
  ((⟨table.1.1.weight,P.1.1,Q.1.1⟩,wrap 64 4 [merged.1.2,table.1.2,P.1.2,Q.1.2]),merged.2+table.2+P.2+Q.2+12)

set_option cleanup.letToHave false in
def descriptorWithExtras (input : BinarySmallUniformCompiler.Input) : ((BinaryStoredOverlapEnvironment.Segment 4 9 × Trace) × ℕ) × ℕ :=
  let merged := childWithExtras input
  let table := BinaryThreeFactoryMeasured.descriptorWithExtras merged.1.1.1
  let P := BinaryLifetimeArrayExtras.build 9 (fun slot => BinarySmallUniformSplitMeasured.splitWithExtras input.l0 input.l1 (table.1.1.1.P.read slot))
  let Q := BinaryLifetimeArrayExtras.build 9 (fun slot => BinarySmallUniformSplitMeasured.splitWithExtras input.l0 input.l1 (table.1.1.1.Q.read slot))
  (assemble merged.1 table.1 P.1 Q.1,merged.2+table.2+P.2+Q.2)

def descriptor (input : BinarySmallUniformCompiler.Input) : (BinaryStoredOverlapEnvironment.Segment 4 9 × Trace) × ℕ :=
  (descriptorWithExtras input).1

theorem descriptorWithExtras_compat (input : BinarySmallUniformCompiler.Input) :
    (descriptorWithExtras input).1 = descriptor input := rfl

theorem descriptor_record (input : BinarySmallUniformCompiler.Input) :
    descriptor input =
  let merged := child input
  let table := BinaryThreeFactoryMeasured.descriptor merged.1.1
  let P := BinaryLifetimeArrayMeasured.build 9 (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.P.read slot))
  let Q := BinaryLifetimeArrayMeasured.build 9 (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.Q.read slot))
  assemble merged table P Q := by
  simp only [childWithExtras_compat,descriptor,descriptorWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryThreeFactoryMeasured.orderedWithExtras_compat,BinaryThreeFactoryMeasured.descriptorWithExtras_compat,BinarySmallUniformPreparationMeasured.prepareWithExtras_compat,BinarySmallUniformSplitMeasured.splitWithExtras_compat]

theorem descriptor_eq (input : BinarySmallUniformCompiler.Input) : descriptor input =
    let merged := child input
    let table := BinaryThreeFactoryMeasured.descriptor merged.1.1
    assemble merged table
      (BinaryLifetimeArrayMeasured.build 9 (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.P.read slot)))
      (BinaryLifetimeArrayMeasured.build 9 (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.Q.read slot))) := by
  exact descriptor_record input

theorem descriptor_data (input : BinarySmallUniformCompiler.Input) :
    (descriptor input).1.1 = (BinarySmallUniformDescriptorLifetime.descriptorWithTrace input).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,descriptor_record,assemble,BinarySmallUniformDescriptorLifetime.descriptorWithTrace,child_data,
    BinaryThreeFactoryMeasured.descriptor_data,BinaryLifetimeArrayMeasured.build_data,BinaryLifetimeArray.build_erases,
    BinarySmallUniformSplitMeasured.split_data]

def arrayPrice (s : ℕ) : ℕ := 9*BinarySmallUniformSplitMeasured.workEnvelope s+6400
def arrayEnvelope (s : ℕ) : ℕ := 10*BinarySmallUniformSplitMeasured.envelope s+BinaryLifetimeArrayMeasured.storageReserve 9+28

def workEnvelope (s : ℕ) : ℕ := childPrice s+BinaryThreeFactoryMeasured.workEnvelope (expressionHeightBudget s 1)+
  2*arrayPrice (expressionHeightBudget s 19)+12

def envelope (s : ℕ) : ℕ := childEnvelope s+BinaryThreeFactoryMeasured.envelope (expressionHeightBudget s 1)+
  2*arrayEnvelope (expressionHeightBudget s 19)+96

theorem assemble_bounds (merged : (BinaryThreeInputCompiler.Input × Trace) × ℕ)
    (table : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ)
    (P Q : (FixedArrayTable 9 (FixedArrayTable 4 SignedWord) × Trace) × ℕ)
    (W T A B F G : ℕ)
    (hm : merged.2 ≤ W ∧ usage merged.1.2 ≤ F) (ht : table.2 ≤ T ∧ usage table.1.2 ≤ G)
    (hp : P.2 ≤ A ∧ usage P.1.2 ≤ B) (hq : Q.2 ≤ A ∧ usage Q.1.2 ≤ B) :
    (assemble merged table P Q).2 ≤ W+T+2*A+12 ∧ usage (assemble merged table P Q).1.2 ≤ F+G+2*B+96 := by
  have hw := wrap_usage 64 4 [merged.1.2,table.1.2,P.1.2,Q.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change merged.2+table.2+P.2+Q.2+12 ≤ _ ∧ usage (wrap 64 4 [merged.1.2,table.1.2,P.1.2,Q.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem descriptor_bounds (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySmallUniformFactoryWork.InputHeight input s) :
    (descriptor input).2 ≤ workEnvelope s ∧ usage (descriptor input).1.2 ≤ envelope s := by
  let merged := child input
  let table := BinaryThreeFactoryMeasured.descriptor merged.1.1
  let P := BinaryLifetimeArrayMeasured.build 9 (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.P.read slot))
  let Q := BinaryLifetimeArrayMeasured.build 9 (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.Q.read slot))
  have hChildE := (child_data input).trans (BinarySmallUniformDescriptorLifetime.childWithTrace_erasure input hC)
  have hChildC : merged.1.1.Canonical := by rw [hChildE]; exact BinarySmallUniformCompiler.child_canonical input hC
  have hChildH := BinarySmallUniformFactoryWork.child_height input hC s hs hH
  have hs1 : 3 ≤ expressionHeightBudget s 1 := hs.trans (expressionHeightBudget_ge_input s 1)
  have hTableE := (BinaryThreeFactoryMeasured.descriptor_data merged.1.1).trans
    (BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure merged.1.1 hChildC)
  have hTableC : table.1.1.Canonical := by rw [hTableE]; exact BinaryThreeSpecCompiler.descriptor_canonical merged.1.1 hChildC
  have hOldHeight := BinaryUnorderedThreeFactoryWork.descriptor_height
    (BinarySmallUniformCompiler.child input) (BinarySmallUniformCompiler.child_canonical input hC)
    (expressionHeightBudget s 1) hs1 hChildH
  rw [expressionHeightBudget_comp] at hOldHeight
  norm_num only [show 1+18 = (19 : ℕ) from rfl] at hOldHeight
  have hTableH : SegmentHeight table.1.1 (expressionHeightBudget s 19) := by rw [hTableE,hChildE]; exact hOldHeight
  have hm19 := expressionHeightBudget_ge_input s 19
  have hFirst := hH.2.1.mono hm19
  have hSecond := hH.2.2.1.mono hm19
  have hPItem := fun slot => BinarySmallUniformSplitMeasured.split_bounds input.l0 input.l1 (table.1.1.P.read slot)
    hC.2.1 hC.2.2.1 (hTableC.2.1 slot) _ hFirst hSecond (fun j => (hTableH.2 slot j).1)
  have hQItem := fun slot => BinarySmallUniformSplitMeasured.split_bounds input.l0 input.l1 (table.1.1.Q.read slot)
    hC.2.1 hC.2.2.1 (hTableC.2.2 slot) _ hFirst hSecond (fun j => (hTableH.2 slot j).2)
  have hPW := BinaryLifetimeArrayMeasured.build_work_bound 9
    (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.P.read slot)) _ (fun slot => (hPItem slot).1)
  have hQW := BinaryLifetimeArrayMeasured.build_work_bound 9
    (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.Q.read slot)) _ (fun slot => (hQItem slot).1)
  have hPU := BinaryLifetimeArrayMeasured.build_bounds 9
    (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.P.read slot))
    (BinarySmallUniformSplitMeasured.envelope (expressionHeightBudget s 19)) (BinarySmallUniformSplitMeasured.envelope (expressionHeightBudget s 19))
    (by intro slot; have h := (hPItem slot).2; unfold usage at h; omega)
    (by intro slot; have h := (hPItem slot).2; unfold usage at h; omega)
  have hQU := BinaryLifetimeArrayMeasured.build_bounds 9
    (fun slot => BinarySmallUniformSplitMeasured.split input.l0 input.l1 (table.1.1.Q.read slot))
    (BinarySmallUniformSplitMeasured.envelope (expressionHeightBudget s 19)) (BinarySmallUniformSplitMeasured.envelope (expressionHeightBudget s 19))
    (by intro slot; have h := (hQItem slot).2; unfold usage at h; omega)
    (by intro slot; have h := (hQItem slot).2; unfold usage at h; omega)
  have hP : P.2 ≤ arrayPrice (expressionHeightBudget s 19) ∧ usage P.1.2 ≤ arrayEnvelope (expressionHeightBudget s 19) :=
    ⟨hPW,hPU.trans_eq (by unfold arrayEnvelope; omega)⟩
  have hQ : Q.2 ≤ arrayPrice (expressionHeightBudget s 19) ∧ usage Q.1.2 ≤ arrayEnvelope (expressionHeightBudget s 19) :=
    ⟨hQW,hQU.trans_eq (by unfold arrayEnvelope; omega)⟩
  have hMerged := child_bounds input hC s hH
  have hTable := BinaryThreeFactoryMeasured.descriptor_bounds merged.1.1 hChildC _ hs1 (by rw [hChildE]; exact hChildH)
  have hResult := assemble_bounds merged table P Q _ _ _ _ _ _ hMerged hTable hP hQ
  rw [descriptor_eq]
  simpa only [merged,table,P,Q,workEnvelope,envelope] using hResult

theorem all_prefix (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySmallUniformFactoryWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptor input).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((descriptor input).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptor_bounds input hC s hs hH).2 borrowed steps

end Blotto.BinarySmallUniformDescriptorMeasured
