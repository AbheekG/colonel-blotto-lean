import Blotto.BinaryScalarTape
import Blotto.BinaryNestedFirstProfileLifetime
import Blotto.BinaryNestedSelectedRegimePrefixLifetime

/-! The already selected first interior regime executes its complete traced
eighteen-slot ordered profile; the other regimes retain their shared inputs. -/
namespace Blotto.BinaryNestedFirstSelectedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18
abbrev Selected := BinaryNestedSelectedRegimePrefixLifetime.Prepared × Fin 3
abbrev Result := Sum Segment (Selected × Option Segment)

def runWithTrace (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : Result × Trace :=
  let prior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input
  match prior.1 with
  | Sum.inl table => (Sum.inl table,wrap 24 2 [prior.2])
  | Sum.inr selected =>
      if selected.2 = 0 then
        let first := BinaryNestedFirstProfileLifetime.profileWithTrace selected.1.1.1 K bits
        (Sum.inr (selected,some first.1),wrap 24 2 [prior.2,first.2])
      else (Sum.inr (selected,none),wrap 24 2 [prior.2])

def oldResult (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : Result :=
  match BinaryNestedSelectedRegimePrefixLifetime.oldResult input with
  | Sum.inl table => Sum.inl table
  | Sum.inr selected =>
      if selected.2 = 0 then
        Sum.inr (selected,some (BinarySegmentAssembly.padRight
          (BinaryNestedFirstConditional.firstProfile selected.1.1.1 K bits) 9 0))
      else Sum.inr (selected,none)

theorem selected_sorted (input : Input) (hC : input.Canonical) (selected : Selected)
    (hSelected : (BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input).1 = Sum.inr selected) :
    selected.1.1.1 = BinaryNestedTerminalInput.sortedInput input := by
  have hOld := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_erasure input hC
  rw [hSelected] at hOld
  unfold BinaryNestedSelectedRegimePrefixLifetime.oldResult
    BinaryNestedInteriorPrefixLifetime.oldResult BinaryNestedClassifyLifetime.oldClassify at hOld
  cases h : BinaryNestedBoundaryLifetime.oldBoundary input with
  | some table => simp [h] at hOld
  | none =>
      simp only [h] at hOld
      have hPair := Sum.inr.inj hOld
      exact congrArg (fun x : Selected => x.1.1.1) hPair

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
      have hSorted := selected_sorted input hC selected h
      have hSortedC : selected.1.1.1.Canonical := by
        rw [hSorted]
        exact BinaryNestedTerminalInput.sortedInput_canonical input hC
      rw [h] at hPrior
      rw [← hPrior]
      simp only [h]
      split
      · simp only [BinaryNestedFirstProfileLifetime.profileWithTrace_erasure _ hSortedC]
      · rfl

def envelope (s K : ℕ) : ℕ :=
  BinaryNestedSelectedRegimePrefixLifetime.envelope s +
    BinaryNestedFirstProfileLifetime.envelope s K + 64

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
    split
    · have hSorted := selected_sorted input hC selected hSelected
      have hSortedC : selected.1.1.1.Canonical := by
        rw [hSorted]
        exact BinaryNestedTerminalInput.sortedInput_canonical input hC
      have hSortedH : BinaryNestedParameterWork.InputHeight selected.1.1.1 s := by
        rw [hSorted]
        exact BinaryNestedSpecFactoryWork.sortedInput_height input hC s hH
      have hFirst := BinaryNestedFirstProfileLifetime.profileWithTrace_usage selected.1.1.1
        hSortedC s hs hSortedH K bits
      have hw := wrap_usage 24 2 [prior.2,
        (BinaryNestedFirstProfileLifetime.profileWithTrace selected.1.1.1 K bits).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [prior.2,
        (BinaryNestedFirstProfileLifetime.profileWithTrace selected.1.1.1 K bits).2]) ≤ _
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

end Blotto.BinaryNestedFirstSelectedLifetime
