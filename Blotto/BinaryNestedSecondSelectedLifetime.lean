import Blotto.BinaryScalarTape
import Blotto.BinaryNestedSecondProfileLifetime
import Blotto.BinaryNestedFirstSelectedLifetime

/-! A single reached regime selection now executes the complete first or
second ordered interior profile. The third regime retains its shared inputs. -/
namespace Blotto.BinaryNestedSecondSelectedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18
abbrev Selected := BinaryNestedFirstSelectedLifetime.Selected
abbrev Result := BinaryNestedFirstSelectedLifetime.Result

def runWithTrace (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : Result × Trace :=
  let prior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input
  match prior.1 with
  | Sum.inl table => (Sum.inl table,wrap 24 2 [prior.2])
  | Sum.inr selected =>
      if selected.2 = 0 then
        let first := BinaryNestedFirstProfileLifetime.profileWithTrace selected.1.1.1 K bits
        (Sum.inr (selected,some first.1),wrap 24 2 [prior.2,first.2])
      else if selected.2 = 1 then
        let second := BinaryNestedSecondProfileLifetime.profileWithTrace
          selected.1.1.1 selected.1.2 K bits
        (Sum.inr (selected,some second.1),wrap 24 2 [prior.2,second.2])
      else (Sum.inr (selected,none),wrap 24 2 [prior.2])

def oldResult (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : Result :=
  match BinaryNestedSelectedRegimePrefixLifetime.oldResult input with
  | Sum.inl table => Sum.inl table
  | Sum.inr selected =>
      if selected.2 = 0 then
        Sum.inr (selected,some (BinarySegmentAssembly.padRight
          (BinaryNestedFirstConditional.firstProfile selected.1.1.1 K bits) 9 0))
      else if selected.2 = 1 then
        Sum.inr (selected,some (BinaryNestedProfileCompiler.secondProfile selected.1.1.1 K bits))
      else Sum.inr (selected,none)

theorem selected_contract (input : Input) (hC : input.Canonical) (selected : Selected)
    (hSelected : (BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input).1 = Sum.inr selected) :
    selected.1.1.1 = BinaryNestedTerminalInput.sortedInput input ∧
      selected.1.2 = BinaryNestedProfileCompiler.parameters selected.1.1.1 := by
  have hOld := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_erasure input hC
  rw [hSelected] at hOld
  unfold BinaryNestedSelectedRegimePrefixLifetime.oldResult
    BinaryNestedInteriorPrefixLifetime.oldResult BinaryNestedClassifyLifetime.oldClassify at hOld
  cases h : BinaryNestedBoundaryLifetime.oldBoundary input with
  | some table => simp [h] at hOld
  | none =>
      simp only [h] at hOld
      have hPair := Sum.inr.inj hOld
      constructor
      · exact congrArg (fun x : Selected => x.1.1.1) hPair
      · rw [hPair]

theorem runWithTrace_erasure (input : Input) (hC : input.Canonical)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (runWithTrace input K bits).1 = oldResult input K bits := by
  have hPrior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_erasure input hC
  unfold runWithTrace oldResult
  cases h : (BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input).1 with
  | inl table =>
      rw [h] at hPrior
      rw [← hPrior]
      simp only [h]
  | inr selected =>
      have hContract := selected_contract input hC selected h
      have hSortedC : selected.1.1.1.Canonical := by
        rw [hContract.1]
        exact BinaryNestedTerminalInput.sortedInput_canonical input hC
      rw [h] at hPrior
      rw [← hPrior]
      simp only [h]
      split
      · simp only [BinaryNestedFirstProfileLifetime.profileWithTrace_erasure _ hSortedC]
      · split
        · simp only [BinaryNestedSecondProfileLifetime.profileWithTrace_erasure
            _ _ hSortedC hContract.2]
        · rfl

def envelope (s K : ℕ) : ℕ :=
  BinaryNestedSelectedRegimePrefixLifetime.envelope s +
    BinaryNestedFirstProfileLifetime.envelope s K +
    BinaryNestedSecondProfileLifetime.envelope s K + 128

theorem runWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (runWithTrace input K bits).2 ≤ envelope s K := by
  let prior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input
  have hPrior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_usage input hC s hs hH
  change usage prior.2 ≤ _ at hPrior
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [prior.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [prior.2]) ≤ _
    unfold envelope
    omega
  · rename_i selected hSelected
    have hContract := selected_contract input hC selected hSelected
    have hSortedC : selected.1.1.1.Canonical := by
      rw [hContract.1]
      exact BinaryNestedTerminalInput.sortedInput_canonical input hC
    have hSortedH : BinaryNestedParameterWork.InputHeight selected.1.1.1 s := by
      rw [hContract.1]
      exact BinaryNestedSpecFactoryWork.sortedInput_height input hC s hH
    have hFirst := BinaryNestedFirstProfileLifetime.profileWithTrace_usage selected.1.1.1
      hSortedC s hs hSortedH K bits
    have hSecond := BinaryNestedSecondProfileLifetime.profileWithTrace_usage
      selected.1.1.1 selected.1.2 hSortedC hContract.2 s hs hSortedH K bits
    split
    · have hw := wrap_usage 24 2 [prior.2,
        (BinaryNestedFirstProfileLifetime.profileWithTrace selected.1.1.1 K bits).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [prior.2,
        (BinaryNestedFirstProfileLifetime.profileWithTrace selected.1.1.1 K bits).2]) ≤ _
      unfold envelope
      omega
    · split
      · have hw := wrap_usage 24 2 [prior.2,
          (BinaryNestedSecondProfileLifetime.profileWithTrace selected.1.1.1 selected.1.2 K bits).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        change usage (wrap 24 2 [prior.2,
          (BinaryNestedSecondProfileLifetime.profileWithTrace selected.1.1.1 selected.1.2 K bits).2]) ≤ _
        unfold envelope
        omega
      · have hw := wrap_usage 24 2 [prior.2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        change usage (wrap 24 2 [prior.2]) ≤ _
        unfold envelope
        omega

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace input K bits).2 steps ≤ borrowed + envelope s K ∧
    framePeak ((runWithTrace input K bits).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage input hC s hs hH K bits) borrowed steps

end Blotto.BinaryNestedSecondSelectedLifetime
