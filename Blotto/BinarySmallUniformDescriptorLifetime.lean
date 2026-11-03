import Blotto.BinarySmallUniformSplitLifetime
import Blotto.BinaryUnorderedThreeLifetime

/-! A traced merged child and all eighteen endpoint splits build the actual
nine-slot small-uniform descriptor, retaining every array prefix. -/
namespace Blotto.BinarySmallUniformDescriptorLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryFactoryHeight
set_option maxHeartbeats 3000000

def childWithTrace (input : BinarySmallUniformCompiler.Input) :
    BinaryThreeInputCompiler.Input × Trace :=
  let total := BinaryQuadraticLifetime.applyWithTrace .add input.l0 input.l1
  (⟨input.B,total.1,input.l2,input.l3,BinaryExpressionCompiler.Constant.one.word⟩,
    wrap 16 2 [total.2])

theorem childWithTrace_erasure (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical) :
    (childWithTrace input).1 = BinarySmallUniformCompiler.child input := by
  unfold childWithTrace BinarySmallUniformCompiler.child
  dsimp only
  rw [BinaryQuadraticLifetime.applyWithTrace_state .add input.l0 input.l1 hC.2.1.1 hC.2.2.1.1]

def childEnvelope (s : ℕ) : ℕ := opcodeEnvelope (2*s+1) + 24

theorem childWithTrace_usage (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hH : BinarySmallUniformFactoryWork.InputHeight input s) :
    usage (childWithTrace input).2 ≤ childEnvelope s := by
  have hL : width input.l0 ≤ 2*s+1 := by
    have h := hC.2.1.2.trans (rationalWordWidth_of_height hH.2.1)
    omega
  have hR : width input.l1 ≤ 2*s+1 := by
    have h := hC.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.1)
    omega
  have hOp := opcode_usage .add input.l0 input.l1 (2*s+1) hL hR
  have hw := wrap_usage 16 2 [(BinaryQuadraticLifetime.applyWithTrace .add input.l0 input.l1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 16 2 [(BinaryQuadraticLifetime.applyWithTrace .add input.l0 input.l1).2]) ≤ _
  unfold childEnvelope
  omega

def descriptorWithTrace (input : BinarySmallUniformCompiler.Input) :
    BinaryStoredOverlapEnvironment.Segment 4 9 × Trace :=
  let child := childWithTrace input
  let table := BinaryUnorderedThreeLifetime.descriptorWithTrace child.1
  let P := BinaryLifetimeArray.build 9 (fun slot =>
    BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.1.P.read slot))
  let Q := BinaryLifetimeArray.build 9 (fun slot =>
    BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.1.Q.read slot))
  (⟨table.1.weight,P.1,Q.1⟩,wrap 64 4 [child.2,table.2,P.2,Q.2])

-- Specification-only projection; the producer above computes each split once.
private def dataFromTable (input : BinarySmallUniformCompiler.Input)
    (table : BinaryStoredOverlapEnvironment.Segment 3 9) : BinaryStoredOverlapEnvironment.Segment 4 9 :=
  ⟨table.weight,
    (BinaryLifetimeArray.build 9 (fun slot =>
      BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.P.read slot))).1,
    (BinaryLifetimeArray.build 9 (fun slot =>
      BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.Q.read slot))).1⟩

private theorem data_projection (input : BinarySmallUniformCompiler.Input) :
    (descriptorWithTrace input).1 =
      dataFromTable input
        (BinaryUnorderedThreeLifetime.descriptorWithTrace (childWithTrace input).1).1 := by
  simp only [descriptorWithTrace,dataFromTable]

private theorem dataFromTable_erasure (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (table : BinaryStoredOverlapEnvironment.Segment 3 9) (hTableC : table.Canonical) :
    dataFromTable input table =
      ⟨table.weight,FixedArrayTable.ofFn (fun slot => BinarySmallUniformCompiler.split input.l0 input.l1 (table.P.read slot)),
        FixedArrayTable.ofFn (fun slot => BinarySmallUniformCompiler.split input.l0 input.l1 (table.Q.read slot))⟩ := by
  have hPF : (fun slot : Fin 9 => (BinarySmallUniformSplitLifetime.splitWithTrace
      input.l0 input.l1 (table.P.read slot)).1) =
      (fun slot : Fin 9 => BinarySmallUniformCompiler.split input.l0 input.l1 (table.P.read slot)) := by
    funext slot
    exact BinarySmallUniformSplitLifetime.splitWithTrace_erasure _ _ _ hC.2.1 hC.2.2.1 (hTableC.2.1 slot)
  have hQF : (fun slot : Fin 9 => (BinarySmallUniformSplitLifetime.splitWithTrace
      input.l0 input.l1 (table.Q.read slot)).1) =
      (fun slot : Fin 9 => BinarySmallUniformCompiler.split input.l0 input.l1 (table.Q.read slot)) := by
    funext slot
    exact BinarySmallUniformSplitLifetime.splitWithTrace_erasure _ _ _ hC.2.1 hC.2.2.1 (hTableC.2.2 slot)
  change (⟨table.weight, FixedArrayTable.ofFn (fun slot : Fin 9 =>
      (BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.P.read slot)).1),
      FixedArrayTable.ofFn (fun slot : Fin 9 =>
      (BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.Q.read slot)).1)⟩ :
      BinaryStoredOverlapEnvironment.Segment 4 9) = _
  rw [hPF,hQF]

theorem descriptorWithTrace_erasure (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical) :
    (descriptorWithTrace input).1 = BinarySmallUniformCompiler.descriptor input := by
  let child := childWithTrace input
  let table := BinaryUnorderedThreeLifetime.descriptorWithTrace child.1
  have hChild := childWithTrace_erasure input hC
  have hChildC : child.1.Canonical := by
    rw [hChild]
    exact BinarySmallUniformCompiler.child_canonical input hC
  have hTable := BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure child.1 hChildC
  have hOldC := BinaryThreeSpecCompiler.descriptor_canonical
    (BinarySmallUniformCompiler.child input) (BinarySmallUniformCompiler.child_canonical input hC)
  calc
    _ = dataFromTable input table.1 := by
      simpa only [table,child] using data_projection input
    _ = dataFromTable input (BinaryThreeSpecCompiler.descriptor child.1) := by rw [hTable]
    _ = dataFromTable input (BinaryThreeSpecCompiler.descriptor (BinarySmallUniformCompiler.child input)) := by rw [hChild]
    _ = BinarySmallUniformCompiler.descriptor input := by
      simpa only [BinarySmallUniformCompiler.descriptor] using
        dataFromTable_erasure input hC (BinaryThreeSpecCompiler.descriptor (BinarySmallUniformCompiler.child input)) hOldC

def arrayEnvelope (s : ℕ) : ℕ :=
  9 * BinarySmallUniformSplitLifetime.envelope s + BinarySmallUniformSplitLifetime.envelope s + 223

def envelope (s : ℕ) : ℕ :=
  childEnvelope s + BinaryUnorderedThreeLifetime.envelope (expressionHeightBudget s 1) +
    2 * arrayEnvelope (expressionHeightBudget s 19) + 96

theorem descriptorWithTrace_usage (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySmallUniformFactoryWork.InputHeight input s) :
    usage (descriptorWithTrace input).2 ≤ envelope s := by
  let child := childWithTrace input
  let table := BinaryUnorderedThreeLifetime.descriptorWithTrace child.1
  let P := BinaryLifetimeArray.build 9 (fun slot =>
    BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.1.P.read slot))
  let Q := BinaryLifetimeArray.build 9 (fun slot =>
    BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.1.Q.read slot))
  have hChildE := childWithTrace_erasure input hC
  have hChildC : child.1.Canonical := by
    rw [hChildE]
    exact BinarySmallUniformCompiler.child_canonical input hC
  have hChildHeight := BinarySmallUniformFactoryWork.child_height input hC s hs hH
  have hs1 : 3 ≤ expressionHeightBudget s 1 := hs.trans (expressionHeightBudget_ge_input s 1)
  have hTableE := BinaryUnorderedThreeLifetime.descriptorWithTrace_erasure child.1 hChildC
  have hTableC : table.1.Canonical := by
    rw [hTableE]
    exact BinaryThreeSpecCompiler.descriptor_canonical child.1 hChildC
  have hOldTable := BinaryUnorderedThreeFactoryWork.descriptor_height
    (BinarySmallUniformCompiler.child input) (BinarySmallUniformCompiler.child_canonical input hC)
    (expressionHeightBudget s 1) hs1 hChildHeight
  rw [expressionHeightBudget_comp] at hOldTable
  norm_num only [show 1+18 = (19 : ℕ) from rfl] at hOldTable
  have hTableHeight : SegmentHeight table.1 (expressionHeightBudget s 19) := by
    rw [hTableE,hChildE]
    exact hOldTable
  have hm19 := expressionHeightBudget_ge_input s 19
  have hFirst : RationalHeight (value input.l0) (expressionHeightBudget s 19) := hH.2.1.mono hm19
  have hSecond : RationalHeight (value input.l1) (expressionHeightBudget s 19) := hH.2.2.1.mono hm19
  have hPItem : ∀ slot,usage (BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1
      (table.1.P.read slot)).2 ≤ BinarySmallUniformSplitLifetime.envelope (expressionHeightBudget s 19) := by
    intro slot
    exact BinarySmallUniformSplitLifetime.splitWithTrace_usage input.l0 input.l1 (table.1.P.read slot)
      hC.2.1 hC.2.2.1 (hTableC.2.1 slot) _ hFirst hSecond
      (fun j => (hTableHeight.2 slot j).1)
  have hQItem : ∀ slot,usage (BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1
      (table.1.Q.read slot)).2 ≤ BinarySmallUniformSplitLifetime.envelope (expressionHeightBudget s 19) := by
    intro slot
    exact BinarySmallUniformSplitLifetime.splitWithTrace_usage input.l0 input.l1 (table.1.Q.read slot)
      hC.2.1 hC.2.2.1 (hTableC.2.2 slot) _ hFirst hSecond
      (fun j => (hTableHeight.2 slot j).2)
  have hP := array_usage 9 (fun slot => BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.1.P.read slot))
    (BinarySmallUniformSplitLifetime.envelope (expressionHeightBudget s 19))
    (BinarySmallUniformSplitLifetime.envelope (expressionHeightBudget s 19))
    (by intro slot; have he := hPItem slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at he; omega)
    (by intro slot; have he := hPItem slot; unfold usage at he; omega)
  have hQ := array_usage 9 (fun slot => BinarySmallUniformSplitLifetime.splitWithTrace input.l0 input.l1 (table.1.Q.read slot))
    (BinarySmallUniformSplitLifetime.envelope (expressionHeightBudget s 19))
    (BinarySmallUniformSplitLifetime.envelope (expressionHeightBudget s 19))
    (by intro slot; have he := hQItem slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at he; omega)
    (by intro slot; have he := hQItem slot; unfold usage at he; omega)
  have hChildU := childWithTrace_usage input hC s hH
  have hTableU := BinaryUnorderedThreeLifetime.descriptorWithTrace_usage child.1 hChildC _ hs1 (by rw [hChildE]; exact hChildHeight)
  change usage child.2 ≤ _ at hChildU
  change usage table.2 ≤ _ at hTableU
  change usage P.2 ≤ _ at hP
  change usage Q.2 ≤ _ at hQ
  have hw := wrap_usage 64 4 [child.2,table.2,P.2,Q.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 64 4 [child.2,table.2,P.2,Q.2]) ≤ _
  unfold envelope arrayEnvelope
  omega

theorem all_prefix (input : BinarySmallUniformCompiler.Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinarySmallUniformFactoryWork.InputHeight input s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptorWithTrace input).2 steps ≤ borrowed + envelope s ∧
    framePeak ((descriptorWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptorWithTrace_usage input hC s hs hH) borrowed steps

end Blotto.BinarySmallUniformDescriptorLifetime
