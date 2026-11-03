import Blotto.BinaryScalarTape
import Blotto.BinaryNestedThirdProfileLifetime
import Blotto.BinaryNestedSecondSelectedLifetime

/-! Complete nested profile lifetime: one boundary/sorting/parameter/regime
prefix, the actual selected factory in all three interior regimes, and traced
restoration to the original coordinate order. -/
namespace Blotto.BinaryNestedProfileLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

abbrev Input := BinaryNestedParameters.Input
abbrev Segment := BinaryStoredOverlapEnvironment.Segment 3 18
abbrev Selected := BinaryNestedFirstSelectedLifetime.Selected

def orderedWithTrace (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) : Segment × Trace :=
  if regime = 0 then
    let table := BinaryNestedFirstProfileLifetime.profileWithTrace input K bits
    (table.1,wrap 24 2 [table.2])
  else if regime = 1 then
    let table := BinaryNestedSecondProfileLifetime.profileWithTrace input parameters K bits
    (table.1,wrap 24 2 [table.2])
  else
    let table := BinaryNestedThirdProfileLifetime.profileWithTrace input parameters K bits
    (table.1,wrap 24 2 [table.2])

theorem orderedWithTrace_erasure (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (regime : Fin 3) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (hRegime : regime = BinaryNestedRegimeLifetime.oldSelect input parameters)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (orderedWithTrace input parameters regime K bits).1 = BinaryNestedProfileCompiler.profile input K bits := by
  subst regime
  subst parameters
  by_cases hFirst : BinaryRationalArithmetic.lessEqual input.t
      ((BinaryNestedProfileCompiler.parameters input).read 2) = true
  · simpa only [orderedWithTrace,BinaryNestedRegimeLifetime.oldSelect,
      BinaryNestedProfileCompiler.profile,hFirst,ite_true] using
      BinaryNestedFirstProfileLifetime.profileWithTrace_erasure input hC K bits
  · by_cases hSecond : BinaryRationalArithmetic.lessEqual
        ((BinaryNestedProfileCompiler.parameters input).read 1) input.t = true
    · simpa [orderedWithTrace,BinaryNestedRegimeLifetime.oldSelect,
        BinaryNestedProfileCompiler.profile,hFirst,hSecond] using
        BinaryNestedSecondProfileLifetime.profileWithTrace_erasure input _ hC rfl K bits
    · simpa [orderedWithTrace,BinaryNestedRegimeLifetime.oldSelect,
        BinaryNestedProfileCompiler.profile,hFirst,hSecond] using
        BinaryNestedThirdProfileLifetime.profileWithTrace_erasure input _ hC rfl K bits

def orderedEnvelope (s K : ℕ) : ℕ :=
  BinaryNestedFirstProfileLifetime.envelope s K + BinaryNestedSecondProfileLifetime.envelope s K +
    BinaryNestedThirdProfileLifetime.envelope s K + 128

theorem orderedWithTrace_usage (input : Input) (parameters : FixedArrayTable 9 SignedWord)
    (regime : Fin 3) (hC : input.Canonical)
    (hParameters : parameters = BinaryNestedProfileCompiler.parameters input)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (orderedWithTrace input parameters regime K bits).2 ≤ orderedEnvelope s K := by
  have hFirst := BinaryNestedFirstProfileLifetime.profileWithTrace_usage input hC s hs hH K bits
  have hSecond := BinaryNestedSecondProfileLifetime.profileWithTrace_usage input parameters hC hParameters s hs hH K bits
  have hThird := BinaryNestedThirdProfileLifetime.profileWithTrace_usage input parameters hC hParameters s hs hH K bits
  unfold orderedWithTrace
  split
  · have hw := wrap_usage 24 2 [(BinaryNestedFirstProfileLifetime.profileWithTrace input K bits).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [(BinaryNestedFirstProfileLifetime.profileWithTrace input K bits).2]) ≤ _
    unfold orderedEnvelope
    omega
  · split
    · have hw := wrap_usage 24 2 [(BinaryNestedSecondProfileLifetime.profileWithTrace input parameters K bits).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [(BinaryNestedSecondProfileLifetime.profileWithTrace input parameters K bits).2]) ≤ _
      unfold orderedEnvelope
      omega
    · have hw := wrap_usage 24 2 [(BinaryNestedThirdProfileLifetime.profileWithTrace input parameters K bits).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [(BinaryNestedThirdProfileLifetime.profileWithTrace input parameters K bits).2]) ≤ _
      unfold orderedEnvelope
      omega

theorem selected_contract (input : Input) (hC : input.Canonical) (selected : Selected)
    (hSelected : (BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input).1 = Sum.inr selected) :
    selected.1.1.1 = BinaryNestedTerminalInput.sortedInput input ∧
      selected.1.1.2 = BinaryNestedTerminalInput.ordered input ∧
      selected.1.2 = BinaryNestedProfileCompiler.parameters selected.1.1.1 ∧
      selected.2 = BinaryNestedRegimeLifetime.oldSelect selected.1.1.1 selected.1.2 := by
  have hOld := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_erasure input hC
  rw [hSelected] at hOld
  unfold BinaryNestedSelectedRegimePrefixLifetime.oldResult
    BinaryNestedInteriorPrefixLifetime.oldResult BinaryNestedClassifyLifetime.oldClassify at hOld
  cases h : BinaryNestedBoundaryLifetime.oldBoundary input with
  | some table => simp [h] at hOld
  | none =>
      simp only [h] at hOld
      have hPair := Sum.inr.inj hOld
      rw [hPair]
      exact ⟨rfl,rfl,rfl,rfl⟩

def profileWithTrace (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : Segment × Trace :=
  let prior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input
  match prior.1 with
  | Sum.inl table => (table,wrap 24 2 [prior.2])
  | Sum.inr selected =>
      let child := orderedWithTrace selected.1.1.1 selected.1.2 selected.2 K bits
      BinaryNestedOrderLifetime.restoreWithTrace selected.1.1.2 prior.2 child

def oldResult (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : Segment :=
  match BinaryNestedSelectedRegimePrefixLifetime.oldResult input with
  | Sum.inl table => table
  | Sum.inr selected =>
      let table := BinaryNestedProfileCompiler.profile selected.1.1.1 K bits
      if selected.1.1.2 then table else BinaryNestedSpecProfile.swap table

theorem oldResult_eq_profile (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    oldResult input K bits = BinaryNestedSpecProfile.profile input K bits := by
  unfold oldResult BinaryNestedSelectedRegimePrefixLifetime.oldResult
    BinaryNestedInteriorPrefixLifetime.oldResult BinaryNestedClassifyLifetime.oldClassify
    BinaryNestedBoundaryLifetime.oldBoundary BinaryNestedSpecProfile.profile
  cases hZero : BinaryNestedSpecProfile.qZero input <;>
    cases hOne : BinaryNestedSpecProfile.qOne input <;>
    simp only [hZero,hOne,Bool.false_eq_true,ite_false,ite_true]

theorem profileWithTrace_erasure (input : Input) (hC : input.Canonical)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (profileWithTrace input K bits).1 = BinaryNestedSpecProfile.profile input K bits := by
  suffices h : (profileWithTrace input K bits).1 = oldResult input K bits from
    h.trans (oldResult_eq_profile input K bits)
  have hPrior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_erasure input hC
  unfold profileWithTrace oldResult
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
      have hChild := orderedWithTrace_erasure selected.1.1.1 selected.1.2 selected.2
        hSortedC hContract.2.2.1 hContract.2.2.2 K bits
      rw [h] at hPrior
      rw [← hPrior]
      simp only [h,BinaryNestedOrderLifetime.restoreWithTrace_erasure,hChild]

def envelope (s K : ℕ) : ℕ :=
  BinaryNestedSelectedRegimePrefixLifetime.envelope s + orderedEnvelope s K + 5000 + 192

theorem profileWithTrace_canonical (input : Input) (hC : input.Canonical)
    (K : ℕ) (bits : BinaryScalarTape K) : (profileWithTrace input K bits).1.Canonical := by
  rw [profileWithTrace_erasure input hC K bits]
  exact BinaryNestedSpecProfile.profile_canonical input hC K bits

theorem profileWithTrace_height (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    BinaryFactoryHeight.SegmentHeight (profileWithTrace input K bits).1
      (BinaryNestedOrderedFactoryWork.height s K 83) := by
  rw [profileWithTrace_erasure input hC K bits]
  exact BinaryNestedSpecFactoryWork.profile_height input hC s hs hH K bits

theorem profileWithTrace_usage (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) :
    usage (profileWithTrace input K bits).2 ≤ envelope s K := by
  let prior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace input
  have hPrior := BinaryNestedSelectedRegimePrefixLifetime.runWithTrace_usage input hC s hs hH
  change usage prior.2 ≤ _ at hPrior
  unfold profileWithTrace
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
    have hChild := orderedWithTrace_usage selected.1.1.1 selected.1.2 selected.2
      hSortedC hContract.2.2.1 s hs hSortedH K bits
    have hRestore := BinaryNestedOrderLifetime.restoreWithTrace_usage selected.1.1.2 prior.2
      (orderedWithTrace selected.1.1.1 selected.1.2 selected.2 K bits)
      _ _ hPrior hChild
    exact hRestore.trans (by unfold envelope; omega)

theorem all_prefix (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s)
    (K : ℕ) (bits : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (profileWithTrace input K bits).2 steps ≤ borrowed + envelope s K ∧
    framePeak ((profileWithTrace input K bits).2.take steps) ≤ envelope s K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (profileWithTrace_usage input hC s hs hH K bits) borrowed steps

end Blotto.BinaryNestedProfileLifetime
