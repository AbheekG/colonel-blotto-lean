import Blotto.BinaryNestedOrderLifetime

/-! One boundary dispatch; only interior inputs execute the traced endpoint
sorting and carry its order bit to the later eighteen-slot factory. -/
namespace Blotto.BinaryNestedClassifyLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18
abbrev Result := Sum Segment (Input × Bool)

def classifyWithTrace (input : Input) : Result × Trace :=
  let boundary := BinaryNestedBoundaryLifetime.boundaryWithTrace input
  match boundary.1 with
  | some table => (Sum.inl table,wrap 24 2 [boundary.2])
  | none =>
      let order := BinaryNestedOrderLifetime.orderWithTrace input
      (Sum.inr order.1,wrap 24 2 [boundary.2,order.2])

def oldClassify (input : Input) : Result :=
  match BinaryNestedBoundaryLifetime.oldBoundary input with
  | some table => Sum.inl table
  | none => Sum.inr (BinaryNestedTerminalInput.sortedInput input,
      BinaryNestedTerminalInput.ordered input)

theorem classifyWithTrace_erasure (input : Input) (hC : input.Canonical) :
    (classifyWithTrace input).1 = oldClassify input := by
  have hBoundary := BinaryNestedBoundaryLifetime.boundaryWithTrace_erasure input hC
  unfold classifyWithTrace oldClassify
  cases h : (BinaryNestedBoundaryLifetime.boundaryWithTrace input).1 with
  | some table =>
      rw [h] at hBoundary
      rw [← hBoundary]
      simp only [h]
  | none =>
      rw [h] at hBoundary
      rw [← hBoundary]
      simp only [h,BinaryNestedOrderLifetime.orderWithTrace_erasure input hC]

def envelope (s : ℕ) : ℕ :=
  BinaryNestedBoundaryLifetime.envelope s + BinaryNestedOrderLifetime.orderEnvelope s + 64

theorem classifyWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (classifyWithTrace input).2 ≤ envelope s := by
  let boundary := BinaryNestedBoundaryLifetime.boundaryWithTrace input
  have hBoundary := BinaryNestedBoundaryLifetime.boundaryWithTrace_usage input hC s hs hH
  change usage boundary.2 ≤ _ at hBoundary
  unfold classifyWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [boundary.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [boundary.2]) ≤ _
    unfold envelope
    omega
  · have hOrder := BinaryNestedOrderLifetime.orderWithTrace_usage input hC s hH
    have hw := wrap_usage 24 2 [boundary.2,(BinaryNestedOrderLifetime.orderWithTrace input).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [boundary.2,(BinaryNestedOrderLifetime.orderWithTrace input).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (classifyWithTrace input).2 steps ≤ borrowed + envelope s ∧
    framePeak ((classifyWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (classifyWithTrace_usage input hC s hs hH) borrowed steps

end Blotto.BinaryNestedClassifyLifetime
