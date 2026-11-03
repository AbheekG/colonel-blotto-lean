import Blotto.BinaryNestedParameterLifetime

/-! Boundary dispatch or one sorted interior input with its actual shared
nine-word parameter table. The later three-regime factory consumes this result. -/
namespace Blotto.BinaryNestedInteriorPrefixLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18
abbrev Result := Sum Segment ((Input × Bool) × FixedArrayTable 9 SignedWord)

def runWithTrace (input : Input) : Result × Trace :=
  let classified := BinaryNestedClassifyLifetime.classifyWithTrace input
  match classified.1 with
  | Sum.inl table => (Sum.inl table,wrap 24 2 [classified.2])
  | Sum.inr ordered =>
      let parameters := BinaryNestedParameterLifetime.prepareWithTrace ordered.1
      (Sum.inr (ordered,parameters.1),wrap 24 2 [classified.2,parameters.2])

def oldResult (input : Input) : Result :=
  match BinaryNestedClassifyLifetime.oldClassify input with
  | Sum.inl table => Sum.inl table
  | Sum.inr ordered => Sum.inr (ordered,BinaryNestedProfileCompiler.parameters ordered.1)

theorem classified_interior_sorted (input : Input) (hC : input.Canonical)
    (ordered : Input × Bool)
    (hInterior : (BinaryNestedClassifyLifetime.classifyWithTrace input).1 = Sum.inr ordered) :
    ordered.1 = BinaryNestedTerminalInput.sortedInput input := by
  have hOld := BinaryNestedClassifyLifetime.classifyWithTrace_erasure input hC
  rw [hInterior] at hOld
  unfold BinaryNestedClassifyLifetime.oldClassify at hOld
  cases h : BinaryNestedBoundaryLifetime.oldBoundary input with
  | some table => simp [h] at hOld
  | none =>
      simp only [h] at hOld
      have hPair : ordered =
          (BinaryNestedTerminalInput.sortedInput input,BinaryNestedTerminalInput.ordered input) := by
        exact Sum.inr.inj hOld
      exact congrArg Prod.fst hPair

theorem runWithTrace_erasure (input : Input) (hC : input.Canonical) :
    (runWithTrace input).1 = oldResult input := by
  have hClassified := BinaryNestedClassifyLifetime.classifyWithTrace_erasure input hC
  unfold runWithTrace oldResult
  cases h : (BinaryNestedClassifyLifetime.classifyWithTrace input).1 with
  | inl table =>
      rw [h] at hClassified
      rw [← hClassified]
      simp only [h]
  | inr ordered =>
      have hSorted := classified_interior_sorted input hC ordered h
      have hOrderedC : ordered.1.Canonical := by
        rw [hSorted]
        exact BinaryNestedTerminalInput.sortedInput_canonical input hC
      rw [h] at hClassified
      rw [← hClassified]
      simp only [h,BinaryNestedParameterLifetime.prepareWithTrace_erasure ordered.1 hOrderedC]

def envelope (s : ℕ) : ℕ :=
  BinaryNestedClassifyLifetime.envelope s + BinaryNestedParameterLifetime.envelope s + 64

theorem runWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (runWithTrace input).2 ≤ envelope s := by
  let classified := BinaryNestedClassifyLifetime.classifyWithTrace input
  have hClassified := BinaryNestedClassifyLifetime.classifyWithTrace_usage input hC s hs hH
  change usage classified.2 ≤ _ at hClassified
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [classified.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [classified.2]) ≤ _
    unfold envelope
    omega
  · rename_i ordered hInterior
    have hSorted := classified_interior_sorted input hC ordered hInterior
    have hOrderedC : ordered.1.Canonical := by
      rw [hSorted]
      exact BinaryNestedTerminalInput.sortedInput_canonical input hC
    have hOrderedH : BinaryNestedParameterWork.InputHeight ordered.1 s := by
      rw [hSorted]
      exact BinaryNestedSpecFactoryWork.sortedInput_height input hC s hH
    have hParameters := BinaryNestedParameterLifetime.prepareWithTrace_usage ordered.1
      hOrderedC s hs hOrderedH
    have hw := wrap_usage 24 2
      [classified.2,(BinaryNestedParameterLifetime.prepareWithTrace ordered.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2
      [classified.2,(BinaryNestedParameterLifetime.prepareWithTrace ordered.1).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace input).2 steps ≤ borrowed + envelope s ∧
    framePeak ((runWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage input hC s hs hH) borrowed steps

end Blotto.BinaryNestedInteriorPrefixLifetime
