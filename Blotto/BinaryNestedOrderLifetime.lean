import Blotto.BinaryNestedBoundaryLifetime

/-! Traced sorting of the two free nested endpoints and retained restoration
of the first two coordinates in an eighteen-slot interior profile. -/
namespace Blotto.BinaryNestedOrderLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18

def orderWithTrace (input : Input) : (Input × Bool) × Trace :=
  let compared := BinaryQuadraticExpressionLifetime.compareWithTrace input.a input.d
  let low := BinaryQuadraticLifetime.applyWithTrace .minimum input.a input.d
  let high := BinaryQuadraticLifetime.applyWithTrace .maximum input.a input.d
  (({ input with a := low.1, d := high.1 },compared.1),
    wrap 32 2 [compared.2,low.2,high.2])

theorem orderWithTrace_erasure (input : Input) (hC : input.Canonical) :
    (orderWithTrace input).1 =
      (BinaryNestedTerminalInput.sortedInput input,BinaryNestedTerminalInput.ordered input) := by
  unfold orderWithTrace BinaryNestedTerminalInput.sortedInput BinaryNestedTerminalInput.ordered
  simp only [BinaryQuadraticExpressionLifetime.compareWithTrace_erases,
    BinaryQuadraticLifetime.applyWithTrace_state .minimum _ _ hC.2.1.1 hC.2.2.1.1,
    BinaryQuadraticLifetime.applyWithTrace_state .maximum _ _ hC.2.1.1 hC.2.2.1.1]

def orderEnvelope (s : ℕ) : ℕ :=
  BinaryThreeGeometryLifetime.comparisonEnvelope (2 * s + 1) +
    2 * opcodeEnvelope (2 * s + 1) + 96

theorem orderWithTrace_usage (input : Input) (hC : input.Canonical) (s : ℕ)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (orderWithTrace input).2 ≤ orderEnvelope s := by
  have hA : width input.a ≤ 2 * s + 1 := by
    have h := hC.2.1.2.trans (rationalWordWidth_of_height hH.2.1)
    omega
  have hD : width input.d ≤ 2 * s + 1 := by
    have h := hC.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.1)
    omega
  have hc := BinaryThreeGeometryLifetime.comparison_usage input.a input.d (2*s+1) hA hD
  have hl := opcode_usage .minimum input.a input.d (2*s+1) hA hD
  have hh := opcode_usage .maximum input.a input.d (2*s+1) hA hD
  have hw := wrap_usage 32 2
    [(BinaryQuadraticExpressionLifetime.compareWithTrace input.a input.d).2,
      (BinaryQuadraticLifetime.applyWithTrace .minimum input.a input.d).2,
      (BinaryQuadraticLifetime.applyWithTrace .maximum input.a input.d).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2
    [(BinaryQuadraticExpressionLifetime.compareWithTrace input.a input.d).2,
      (BinaryQuadraticLifetime.applyWithTrace .minimum input.a input.d).2,
      (BinaryQuadraticLifetime.applyWithTrace .maximum input.a input.d).2]) ≤ _
  unfold orderEnvelope
  omega

def swapRowsWithTrace (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) :
    FixedArrayTable 18 (FixedArrayTable 3 SignedWord) × Trace :=
  BinaryLifetimeArray.build 18 (fun slot =>
    BinaryThreeReferenceLifetime.rowWithTrace
      ((rows.read slot).read 1) ((rows.read slot).read 0) ((rows.read slot).read 2))

theorem swapRowsWithTrace_erasure (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) :
    (swapRowsWithTrace rows).1 = FixedArrayTable.ofFn (fun slot =>
      FixedArrayTable.ofFn ![(rows.read slot).read 1,(rows.read slot).read 0,(rows.read slot).read 2]) := by
  rfl

theorem swapRowsWithTrace_usage (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) :
    usage (swapRowsWithTrace rows).2 ≤ 2160 := by
  have hr := fun slot => BinaryThreeReferenceLifetime.rowWithTrace_usage
    ((rows.read slot).read 1) ((rows.read slot).read 0) ((rows.read slot).read 2)
  have h := array_usage 18 (fun slot => BinaryThreeReferenceLifetime.rowWithTrace
    ((rows.read slot).read 1) ((rows.read slot).read 0) ((rows.read slot).read 2)) 74 74
    (by intro slot; have h := hr slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro slot; have h := hr slot; unfold usage at h; omega)
  exact h

def swapWithTrace (table : Segment) : Segment × Trace :=
  let first := swapRowsWithTrace table.P
  let second := swapRowsWithTrace table.Q
  (⟨table.weight,first.1,second.1⟩,wrap 32 2 [first.2,second.2])

theorem swapWithTrace_erasure (table : Segment) :
    (swapWithTrace table).1 = BinaryNestedSpecProfile.swap table := by
  simp only [swapWithTrace,BinaryNestedSpecProfile.swap,swapRowsWithTrace_erasure]

theorem swapWithTrace_usage (table : Segment) : usage (swapWithTrace table).2 ≤ 5000 := by
  have hp := swapRowsWithTrace_usage table.P
  have hq := swapRowsWithTrace_usage table.Q
  have hw := wrap_usage 32 2 [(swapRowsWithTrace table.P).2,(swapRowsWithTrace table.Q).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [(swapRowsWithTrace table.P).2,(swapRowsWithTrace table.Q).2]) ≤ _
  omega

def restoreWithTrace (ordered : Bool) (orderTrace : Trace) (child : Segment × Trace) :
    Segment × Trace :=
  if ordered then (child.1,wrap 32 2 [orderTrace,child.2]) else
    let restored := swapWithTrace child.1
    (restored.1,wrap 32 2 [orderTrace,child.2,restored.2])

theorem restoreWithTrace_erasure (ordered : Bool) (orderTrace : Trace) (child : Segment × Trace) :
    (restoreWithTrace ordered orderTrace child).1 =
      if ordered then child.1 else BinaryNestedSpecProfile.swap child.1 := by
  unfold restoreWithTrace
  split
  · rfl
  · exact swapWithTrace_erasure child.1

theorem restoreWithTrace_usage (ordered : Bool) (orderTrace : Trace) (child : Segment × Trace)
    (C H : ℕ) (hC : usage orderTrace ≤ C) (hH : usage child.2 ≤ H) :
    usage (restoreWithTrace ordered orderTrace child).2 ≤ C + H + 5000 + 96 := by
  have hRestore := swapWithTrace_usage child.1
  unfold restoreWithTrace
  split
  · have hw := wrap_usage 32 2 [orderTrace,child.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    omega
  · have hw := wrap_usage 32 2 [orderTrace,child.2,(swapWithTrace child.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    omega

theorem order_all_prefix (input : Input) (hC : input.Canonical) (s : ℕ)
    (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (orderWithTrace input).2 steps ≤ borrowed + orderEnvelope s ∧
    framePeak ((orderWithTrace input).2.take steps) ≤ orderEnvelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (orderWithTrace_usage input hC s hH) borrowed steps

end Blotto.BinaryNestedOrderLifetime
