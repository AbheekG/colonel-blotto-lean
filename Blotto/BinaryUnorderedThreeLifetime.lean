import Blotto.BinaryOrderedThreeLifetimeBound
import Blotto.BinaryUnorderedThreeFactoryWork

/-! One actual comparison orders the stored input; the complete selected
ordered factory consumes it, then traced reference rows restore the original
coordinates. Both regular and exceptional regimes retain exact old data. -/
namespace Blotto.BinaryUnorderedThreeLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryThreeInputCompiler
set_option maxHeartbeats 2000000

def restoreWithTrace (order : Bool) (orderTrace : Trace) (child : BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) :
    BinaryStoredOverlapEnvironment.Segment 3 9 × Trace :=
  if order then (child.1,wrap 32 2 [orderTrace,child.2]) else
    let restored := BinaryThreeReferenceLifetime.swapWithTrace child.1
    (restored.1,wrap 32 2 [orderTrace,child.2,restored.2])

def descriptorWithTrace (input : Input) : BinaryStoredOverlapEnvironment.Segment 3 9 × Trace :=
  let order := BinaryQuadraticExpressionLifetime.compareWithTrace input.a input.d
  let ordered := if order.1 then input else ⟨input.B,input.d,input.a,input.c,input.p⟩
  let child := BinaryOrderedThreeLifetime.descriptorWithTrace ordered
  restoreWithTrace order.1 order.2 child

theorem descriptorWithTrace_erasure (input : Input) (hC : input.Canonical) :
    (descriptorWithTrace input).1 = BinaryThreeSpecCompiler.descriptor input := by
  unfold descriptorWithTrace restoreWithTrace BinaryThreeSpecCompiler.descriptor BinaryThreeSpecCompiler.ordered
  dsimp only
  simp only [BinaryQuadraticExpressionLifetime.compareWithTrace_erases]
  cases hOrder : BinaryRationalArithmetic.lessEqual input.a input.d
  · simp only [hOrder,Bool.false_eq_true,ite_false,BinaryThreeReferenceLifetime.swapWithTrace_erasure]
    rw [BinaryOrderedThreeLifetime.descriptorWithTrace_erasure
      (⟨input.B,input.d,input.a,input.c,input.p⟩ : Input) ⟨hC.1,hC.2.2.1,hC.2.1,hC.2.2.2.1,hC.2.2.2.2⟩]
  · simp only [hOrder,ite_true]
    exact BinaryOrderedThreeLifetime.descriptorWithTrace_erasure input hC

def envelope (s : ℕ) : ℕ :=
  BinaryThreeGeometryLifetime.comparisonEnvelope (2 * s + 1) + BinaryOrderedThreeLifetimeBound.envelope s + 4096 + 96

theorem restoreWithTrace_usage (order : Bool) (orderTrace : Trace) (child : BinaryStoredOverlapEnvironment.Segment 3 9 × Trace)
    (C H : ℕ) (hC : usage orderTrace ≤ C) (hH : usage child.2 ≤ H) :
    usage (restoreWithTrace order orderTrace child).2 ≤ C + H + 4096 + 96 := by
  have hRestore := BinaryThreeReferenceLifetime.swapWithTrace_usage child.1
  unfold restoreWithTrace
  split
  · have hw := wrap_usage 32 2 [orderTrace,child.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    omega
  · have hw := wrap_usage 32 2 [orderTrace,child.2,(BinaryThreeReferenceLifetime.swapWithTrace child.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    dsimp only
    omega

theorem descriptorWithTrace_usage (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : BinaryOrderedThreeFactoryWork.InputHeight input s) : usage (descriptorWithTrace input).2 ≤ envelope s := by
  let order := BinaryQuadraticExpressionLifetime.compareWithTrace input.a input.d
  let ordered : Input := if order.1 then input else ⟨input.B,input.d,input.a,input.c,input.p⟩
  have hOrdered : ordered = BinaryThreeSpecCompiler.ordered input := by
    dsimp only [ordered,order]
    rw [BinaryQuadraticExpressionLifetime.compareWithTrace_erases]
    rfl
  have hCOrdered : ordered.Canonical := by rw [hOrdered]; exact BinaryThreeSpecCompiler.ordered_canonical input hC
  have hHOrdered : BinaryOrderedThreeFactoryWork.InputHeight ordered s := by
    rw [hOrdered]
    exact BinaryUnorderedThreeFactoryWork.ordered_height input s hHeight
  have hA : width input.a ≤ 2 * s + 1 := by
    have h := hC.2.1.2.trans (rationalWordWidth_of_height hHeight.2.1)
    omega
  have hD : width input.d ≤ 2 * s + 1 := by
    have h := hC.2.2.1.2.trans (rationalWordWidth_of_height hHeight.2.2.1)
    omega
  have hOrder := BinaryThreeGeometryLifetime.comparison_usage input.a input.d (2 * s + 1) hA hD
  have hChild := BinaryOrderedThreeLifetimeBound.descriptorWithTrace_usage ordered hCOrdered s hs hHOrdered
  change usage order.2 ≤ _ at hOrder
  exact restoreWithTrace_usage order.1 order.2 (BinaryOrderedThreeLifetime.descriptorWithTrace ordered) _ _ hOrder hChild

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hHeight : BinaryOrderedThreeFactoryWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptorWithTrace input).2 steps ≤ borrowed + envelope s ∧
      framePeak ((descriptorWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptorWithTrace_usage input hC s hs hHeight) borrowed steps

end Blotto.BinaryUnorderedThreeLifetime
