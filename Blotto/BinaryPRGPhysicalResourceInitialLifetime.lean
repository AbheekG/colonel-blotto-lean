import Blotto.BinaryPRGPhysicalRawRequestLifetime
import Blotto.BooleanArrayIndexEnumeration

/-! The initial resource scan can select its active coordinates from the
physical numerical stores. A Boolean carry stream supplies the indices;
native compatibility tables remain for the subsequent resource state and
updates. This module prices the physical lookup trace, not the already
separate rational comparison work. -/
namespace Blotto.BinaryPRGPhysicalResourceInitialLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime
set_option autoImplicit false
set_option maxHeartbeats 3000000

def resourceStore {n : ℕ} (request : Request n) (rich : Bool) :
    BinaryWordObjectArray.Store n :=
  if rich then request.physical.lengthStore else request.physical.poorStore

def fractionalWithTrace {n : ℕ} (request : Request n) (rich : Bool)
    (index : List Bool) : Option Bool × Trace :=
  let capacity := BinaryWordObjectArrayAccess.getWithTrace request.physical.lengthStore index
  let resource := BinaryWordObjectArrayAccess.getWithTrace (resourceStore request rich) index
  match capacity.1, resource.1 with
  | some cap, some bid =>
      (some ((!BinaryRationalArithmetic.lessEqual bid BinaryRationalOpcode.zero) &&
        (!BinaryRationalArithmetic.lessEqual cap bid)),
        wrap 16 2 [capacity.2,resource.2])
  | _,_ => (none,wrap 16 2 [capacity.2,resource.2])

theorem fractionalWithTrace_state (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (rich : Bool) (index : List Bool) (j : Fin parsed.1.1)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (fractionalWithTrace parsed.1.2 rich index).1 =
      some (BinaryResourceState.fractional
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource j) := by
  have hReads := returned_resource_reads frame parsed hParsed rich index j hIndex
  simp only [fractionalWithTrace,resourceStore,hReads.1,hReads.2,
    BinaryResourceState.fractional]

def lookupBudget {n : ℕ} (request : Request n) (rich : Bool)
    (index : List Bool) : ℕ :=
  BinaryWordObjectArrayAccess.envelope request.physical.lengthStore index.length +
    BinaryWordObjectArrayAccess.envelope (resourceStore request rich) index.length + 24

def lookupEnvelope {n : ℕ} (request : Request n) (rich : Bool)
    (width : ℕ) : ℕ :=
  BinaryWordObjectArrayAccess.envelope request.physical.lengthStore width +
    BinaryWordObjectArrayAccess.envelope (resourceStore request rich) width + 24

theorem readEnvelope_mono {n : ℕ} (store : BinaryWordObjectArray.Store n)
    {a b : ℕ} (h : a ≤ b) :
    BinaryWordObjectArrayAccess.envelope store a ≤
      BinaryWordObjectArrayAccess.envelope store b := by
  unfold BinaryWordObjectArrayAccess.envelope BinaryReferenceVector.readBound
  gcongr

theorem lookupBudget_width {n : ℕ} (request : Request n)
    (rich : Bool) (index : List Bool) (width : ℕ)
    (h : index.length ≤ width) :
    lookupBudget request rich index ≤ lookupEnvelope request rich width := by
  unfold lookupBudget lookupEnvelope
  have hCapacity := readEnvelope_mono request.physical.lengthStore h
  have hResource := readEnvelope_mono (resourceStore request rich) h
  omega

theorem lookupBudget_sum {n : ℕ} (request : Request n)
    (rich : Bool) (indices : List (List Bool)) (width : ℕ)
    (h : ∀ index ∈ indices, index.length ≤ width) :
    (indices.map (lookupBudget request rich)).sum ≤
      indices.length * lookupEnvelope request rich width := by
  induction indices with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons index rest ih =>
      have hi := lookupBudget_width request rich index width (h index (by simp))
      have hr := ih (by intro word hw; exact h word (by simp [hw]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

theorem fractionalWithTrace_usage {n : ℕ} (request : Request n)
    (rich : Bool) (index : List Bool) :
    usage (fractionalWithTrace request rich index).2 ≤ lookupBudget request rich index := by
  let capacity := BinaryWordObjectArrayAccess.getWithTrace request.physical.lengthStore index
  let resource := BinaryWordObjectArrayAccess.getWithTrace (resourceStore request rich) index
  have hCapacity := BinaryWordObjectArrayAccess.get_usage request.physical.lengthStore index
  have hResource := BinaryWordObjectArrayAccess.get_usage (resourceStore request rich) index
  have hWrap := wrap_usage 16 2 [capacity.2,resource.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  have hTrace : (fractionalWithTrace request rich index).2 =
      wrap 16 2 [capacity.2,resource.2] := by
    unfold fractionalWithTrace
    dsimp only [capacity,resource]
    split <;> rfl
  rw [hTrace]
  change usage capacity.2 ≤ _ at hCapacity
  change usage resource.2 ≤ _ at hResource
  unfold lookupBudget
  omega

def scanWithTrace {n : ℕ} (request : Request n) (rich : Bool) :
    List (Fin n) → List (List Bool) → Option (List (Fin n)) × Trace
  | [], [] => (some [],wrap 8 1 [])
  | j::rest, index::indices =>
      let current := fractionalWithTrace request rich index
      let later := scanWithTrace request rich rest indices
      (match current.1,later.1 with
        | some keep,some active => some (if keep then j::active else active)
        | _,_ => none,
        wrapList 1 16 2 [current.2,later.2])
  | _,_ => (none,wrap 8 1 [])

def scanBudget {n : ℕ} (request : Request n) (rich : Bool)
    (items : List (Fin n)) (indices : List (List Bool)) : ℕ :=
  (indices.map (lookupBudget request rich)).sum + 32*(items.length+1)

theorem scanWithTrace_usage {n : ℕ} (request : Request n) (rich : Bool)
    (items : List (Fin n)) (indices : List (List Bool)) :
    usage (scanWithTrace request rich items indices).2 ≤
      scanBudget request rich items indices := by
  induction items generalizing indices with
  | nil =>
      cases indices with
      | nil =>
          have hw := wrap_usage 8 1 ([] : List Trace)
          simp only [List.map_nil,List.sum_nil] at hw
          change usage (scanWithTrace request rich [] []).2 ≤ _
          unfold scanWithTrace scanBudget
          simp only [List.map_nil,List.sum_nil,List.length_nil]
          omega
      | cons index rest =>
          have hw := wrap_usage 8 1 ([] : List Trace)
          simp only [List.map_nil,List.sum_nil] at hw
          change usage (scanWithTrace request rich [] (index::rest)).2 ≤ _
          unfold scanWithTrace scanBudget
          simp only [List.map_cons,List.sum_cons,List.length_nil]
          omega
  | cons j rest ih =>
      cases indices with
      | nil =>
          have hw := wrap_usage 8 1 ([] : List Trace)
          simp only [List.map_nil,List.sum_nil] at hw
          change usage (scanWithTrace request rich (j::rest) []).2 ≤ _
          unfold scanWithTrace scanBudget
          simp only [List.map_nil,List.sum_nil,List.length_cons]
          omega
      | cons index tail =>
          have hc := fractionalWithTrace_usage request rich index
          have ht := ih tail
          have hw := wrapList_usage 1 16 2
            [(fractionalWithTrace request rich index).2,
              (scanWithTrace request rich rest tail).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          change usage (scanWithTrace request rich (j::rest) (index::tail)).2 ≤ _ at hw
          simp only [scanBudget,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
          omega

theorem scanWithTrace_state (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (rich : Bool) (items : List (Fin parsed.1.1)) (indices : List (List Bool))
    (hValues : indices.map BinaryBigEndian.littleValue = items.map Fin.val) :
    (scanWithTrace parsed.1.2 rich items indices).1 =
      some (items.filter (BinaryResourceState.fractional
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource)) := by
  induction items generalizing indices with
  | nil =>
      cases indices with
      | nil => rfl
      | cons index rest => simp at hValues
  | cons j rest ih =>
      cases indices with
      | nil => simp at hValues
      | cons index tail =>
          simp only [List.map_cons,List.cons.injEq] at hValues
          obtain ⟨hHead,hTail⟩ := hValues
          have hc := fractionalWithTrace_state frame parsed hParsed rich index j hHead
          have ht := ih tail hTail
          simp only [scanWithTrace,hc,ht,List.filter_cons]

theorem finRange_values (n : ℕ) :
    (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.finRange_succ,List.map_cons,List.range_succ_eq_map]
      simp only [Fin.val_zero,List.map_map]
      congr 1
      rw [← ih]
      simp only [List.map_map,Function.comp_def,Nat.succ_eq_add_one]
      rfl

def initialScanWithTrace {n : ℕ} (request : Request n) (rich : Bool) :
    Option (List (Fin n)) × Trace :=
  let indices := BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)
  let scan := scanWithTrace request rich (List.finRange n) indices.1
  (scan.1,wrap 32 2 [indices.2,scan.2])

def initialEnvelope {n : ℕ} (request : Request n) (rich : Bool) : ℕ :=
  32*n+16+
    scanBudget request rich (List.finRange n)
      (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1+40

def initialUniformEnvelope {n : ℕ} (request : Request n) (rich : Bool) : ℕ :=
  32*n+16+n*lookupEnvelope request rich (binaryWordWidth n)+32*(n+1)+40

theorem initialEnvelope_uniform {n : ℕ} (request : Request n) (rich : Bool) :
    initialEnvelope request rich ≤ initialUniformEnvelope request rich := by
  let indices := (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1
  have hWidth : ∀ index ∈ indices,index.length ≤ binaryWordWidth n := by
    intro index hIndex
    simpa only [List.length_finRange] using
      BooleanArrayIndexEnumeration.enumerate_width (List.finRange n) index hIndex
  have hLength : indices.length = n := by
    have h := congrArg List.length
      (BooleanArrayIndexEnumeration.enumerate_values (List.finRange n))
    simpa only [List.length_map,List.length_range,List.length_finRange] using h
  have hSum := lookupBudget_sum request rich indices (binaryWordWidth n) hWidth
  unfold initialEnvelope initialUniformEnvelope scanBudget
  rw [hLength] at hSum
  dsimp only [indices] at hSum
  simp only [List.length_finRange] at *
  omega

theorem initialScanWithTrace_usage {n : ℕ} (request : Request n)
    (rich : Bool) :
    usage (initialScanWithTrace request rich).2 ≤ initialEnvelope request rich := by
  have hIndices := BooleanArrayIndexEnumeration.enumerate_usage (List.finRange n)
  have hScan := scanWithTrace_usage request rich (List.finRange n)
    (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1
  have hw := wrap_usage 32 2
    [(BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).2,
      (scanWithTrace request rich (List.finRange n)
        (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (initialScanWithTrace request rich).2 ≤ _
  unfold initialScanWithTrace initialEnvelope
  simp only [List.length_finRange] at *
  omega

theorem initialScanWithTrace_uniform_usage {n : ℕ} (request : Request n)
    (rich : Bool) :
    usage (initialScanWithTrace request rich).2 ≤
      initialUniformEnvelope request rich :=
  (initialScanWithTrace_usage request rich).trans (initialEnvelope_uniform request rich)

theorem initialScanWithTrace_prefix {n : ℕ} (request : Request n)
    (rich : Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (initialScanWithTrace request rich).2 steps ≤
        borrowed+initialEnvelope request rich ∧
      framePeak ((initialScanWithTrace request rich).2.take steps) ≤
        initialEnvelope request rich :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (initialScanWithTrace_usage request rich) borrowed steps

theorem initialScanWithTrace_state (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    (initialScanWithTrace parsed.1.2 rich).1 =
      some ((List.finRange parsed.1.1).filter (BinaryResourceState.fractional
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource)) := by
  unfold initialScanWithTrace
  dsimp only
  apply scanWithTrace_state frame parsed hParsed rich
  rw [finRange_values]
  change List.map BinaryCarryCounter.value
    (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange parsed.1.1)).1 = _
  simpa only [List.length_finRange] using
    BooleanArrayIndexEnumeration.enumerate_values (List.finRange parsed.1.1)

def initialStateWithPhysical (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (_hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    BinaryResourceState.State parsed.1.1 × Trace :=
  let scan := initialScanWithTrace parsed.1.2 rich
  ⟨⟨(BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource,
      scan.1.getD []⟩,scan.2⟩

theorem initialStateWithPhysical_state (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (initialStateWithPhysical frame parsed hParsed rich).1 =
      BinaryResourceState.initial
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource := by
  have hScan := initialScanWithTrace_state frame parsed hParsed rich
  unfold initialStateWithPhysical BinaryResourceState.initial
  dsimp only
  rw [hScan]
  rfl

def initialCertifiedWithPhysical (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length × Trace :=
  let input := BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich
  let canonical := BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich
  let native := BinaryResourcePair.initial input.length input.resource canonical.2.1 canonical.2.2
  let physical := initialStateWithPhysical frame parsed hParsed rich
  have hState : physical.1 = native.state := initialStateWithPhysical_state frame parsed hParsed rich
  (⟨physical.1,
    (by rw [hState]; exact native.canonical),
    (by rw [hState]; exact native.nodup),
    (by rw [hState]; exact native.membership)⟩,physical.2)

private theorem certified_eq_of_state {n : ℕ}
    {capacity : FixedArrayTable n BinaryRationalNormalization.SignedWord}
    (first second : BinaryResourcePair.Certified capacity)
    (h : first.state = second.state) : first = second := by
  cases first with
  | mk state canonical nodup membership =>
      cases second with
      | mk other otherCanonical otherNodup otherMembership =>
          dsimp only at h
          subst other
          rfl

theorem initialCertifiedWithPhysical_state (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (initialCertifiedWithPhysical frame parsed hParsed rich).1 =
      BinaryResourcePair.initial
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2 := by
  apply certified_eq_of_state
  exact initialStateWithPhysical_state frame parsed hParsed rich

def resourceWorkWithPhysical (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    ((Option (BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length) × ℕ) ×
      BinaryGeneralResourceExecution.Charge) × Trace :=
  let initial := initialCertifiedWithPhysical frame parsed hParsed rich
  let later := BinaryGeneralResourceRunWork.run
    (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1 N initial.1 bits
  (later,initial.2)

theorem resourceWorkWithPhysical_state (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysical frame parsed hParsed rich N bits).1.1 =
      (BinaryPRGResourceWork.resourceWork parsed.1.2.logical.request rich N bits).1 := by
  unfold resourceWorkWithPhysical BinaryPRGResourceWork.resourceWork
    BinaryGeneralResourceRunWork.initialRun
  dsimp only
  rw [initialCertifiedWithPhysical_state]
  rw [BinaryGeneralResourceExecution.initialWithCharge_state]

theorem resourceWorkWithPhysical_original (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysical frame parsed hParsed rich N bits).1.1 =
      BinaryLottoResourceInput.run
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich)
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich)
        N bits := by
  rw [resourceWorkWithPhysical_state]
  exact BinaryPRGResourceWork.resourceWork_state parsed.1.2.logical.request rich N bits

theorem resourceWorkWithPhysical_position (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysical frame parsed hParsed rich N bits).1.1.2 ≤ N := by
  rw [resourceWorkWithPhysical_state]
  exact BinaryPRGResourceWork.resourceWork_position parsed.1.2.logical.request rich N bits

theorem resourceWorkWithPhysical_trace (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysical frame parsed hParsed rich N bits).2 =
      (initialScanWithTrace parsed.1.2 rich).2 := by
  rfl

theorem resourceWorkWithPhysical_trace_usage (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    usage (resourceWorkWithPhysical frame parsed hParsed rich N bits).2 ≤
      initialEnvelope parsed.1.2 rich := by
  rw [resourceWorkWithPhysical_trace]
  exact initialScanWithTrace_usage parsed.1.2 rich

theorem resourceWorkWithPhysical_trace_prefix (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (resourceWorkWithPhysical frame parsed hParsed rich N bits).2 steps ≤
        borrowed+initialEnvelope parsed.1.2 rich ∧
      framePeak ((resourceWorkWithPhysical frame parsed hParsed rich N bits).2.take steps) ≤
        initialEnvelope parsed.1.2 rich := by
  rw [resourceWorkWithPhysical_trace]
  exact initialScanWithTrace_prefix parsed.1.2 rich borrowed steps


end Blotto.BinaryPRGPhysicalResourceInitialLifetime
