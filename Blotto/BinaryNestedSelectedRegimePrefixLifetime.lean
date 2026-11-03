import Blotto.BinaryNestedRegimeLifetime

/-! Boundary table or a sorted interior input, one shared parameter table,
and the regime chosen by actual traced comparisons on that returned table. -/
namespace Blotto.BinaryNestedSelectedRegimePrefixLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18
abbrev Prepared := (Input × Bool) × FixedArrayTable 9 SignedWord
abbrev Result := Sum Segment (Prepared × Fin 3)

def runWithTrace (input : Input) : Result × Trace :=
  let prior := BinaryNestedInteriorPrefixLifetime.runWithTrace input
  match prior.1 with
  | Sum.inl table => (Sum.inl table,wrap 24 2 [prior.2])
  | Sum.inr prepared =>
      let selected := BinaryNestedRegimeLifetime.selectWithTrace prepared.1.1 prepared.2
      (Sum.inr (prepared,selected.1),wrap 24 2 [prior.2,selected.2])

def oldResult (input : Input) : Result :=
  match BinaryNestedInteriorPrefixLifetime.oldResult input with
  | Sum.inl table => Sum.inl table
  | Sum.inr prepared =>
      Sum.inr (prepared,BinaryNestedRegimeLifetime.oldSelect prepared.1.1 prepared.2)

theorem interior_contract (input : Input) (hC : input.Canonical) (prepared : Prepared)
    (hInterior : (BinaryNestedInteriorPrefixLifetime.runWithTrace input).1 = Sum.inr prepared) :
    prepared.1.1 = BinaryNestedTerminalInput.sortedInput input ∧
      prepared.2 = BinaryNestedProfileCompiler.parameters prepared.1.1 := by
  have hOld := BinaryNestedInteriorPrefixLifetime.runWithTrace_erasure input hC
  rw [hInterior] at hOld
  unfold BinaryNestedInteriorPrefixLifetime.oldResult
    BinaryNestedClassifyLifetime.oldClassify at hOld
  cases h : BinaryNestedBoundaryLifetime.oldBoundary input with
  | some table => simp [h] at hOld
  | none =>
      simp only [h] at hOld
      have hPrepared : prepared =
          ((BinaryNestedTerminalInput.sortedInput input,BinaryNestedTerminalInput.ordered input),
            BinaryNestedProfileCompiler.parameters (BinaryNestedTerminalInput.sortedInput input)) :=
        Sum.inr.inj hOld
      constructor
      · exact congrArg (fun x : Prepared => x.1.1) hPrepared
      · rw [hPrepared]

theorem runWithTrace_erasure (input : Input) (hC : input.Canonical) :
    (runWithTrace input).1 = oldResult input := by
  have hPrior := BinaryNestedInteriorPrefixLifetime.runWithTrace_erasure input hC
  unfold runWithTrace oldResult
  cases h : (BinaryNestedInteriorPrefixLifetime.runWithTrace input).1 with
  | inl table =>
      rw [h] at hPrior
      rw [← hPrior]
      simp only [h]
  | inr prepared =>
      rw [h] at hPrior
      rw [← hPrior]
      simp only [h,BinaryNestedRegimeLifetime.selectWithTrace_erasure]

def envelope (s : ℕ) : ℕ :=
  BinaryNestedInteriorPrefixLifetime.envelope s +
    BinaryNestedRegimeLifetime.envelope (2 * expressionHeightBudget s 16 + 1) + 64

theorem runWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    usage (runWithTrace input).2 ≤ envelope s := by
  let prior := BinaryNestedInteriorPrefixLifetime.runWithTrace input
  have hPrior := BinaryNestedInteriorPrefixLifetime.runWithTrace_usage input hC s hs hH
  change usage prior.2 ≤ _ at hPrior
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [prior.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [prior.2]) ≤ _
    unfold envelope
    omega
  · rename_i prepared hInterior
    have hContract := interior_contract input hC prepared hInterior
    have hPreparedC : prepared.1.1.Canonical := by
      rw [hContract.1]
      exact BinaryNestedTerminalInput.sortedInput_canonical input hC
    have hPreparedH : BinaryNestedParameterWork.InputHeight prepared.1.1 s := by
      rw [hContract.1]
      exact BinaryNestedSpecFactoryWork.sortedInput_height input hC s hH
    have hCurrent : prepared.2 = (BinaryNestedParameterLifetime.prepareWithTrace prepared.1.1).1 := by
      rw [hContract.2,BinaryNestedParameterLifetime.prepareWithTrace_erasure _ hPreparedC]
    have hSelected := BinaryNestedRegimeLifetime.prepared_usage prepared.1.1 hPreparedC s hs hPreparedH
    rw [← hCurrent] at hSelected
    have hw := wrap_usage 24 2
      [prior.2,(BinaryNestedRegimeLifetime.selectWithTrace prepared.1.1 prepared.2).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2
      [prior.2,(BinaryNestedRegimeLifetime.selectWithTrace prepared.1.1 prepared.2).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace input).2 steps ≤ borrowed + envelope s ∧
    framePeak ((runWithTrace input).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage input hC s hs hH) borrowed steps

end Blotto.BinaryNestedSelectedRegimePrefixLifetime
