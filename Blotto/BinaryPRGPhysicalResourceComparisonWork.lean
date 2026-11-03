import Blotto.BinaryPRGPhysicalResourceRawBound

/-! A single physical lookup pair supplies both the active-coordinate
predicate and its measured Boolean rational-comparison work. The existing
physical scan remains an exact erasure view of this measured path. -/
namespace Blotto.BinaryPRGPhysicalResourceComparisonWork
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime BinaryPRGPhysicalResourceInitialLifetime
set_option autoImplicit false
set_option maxHeartbeats 3000000

def fractionalWithWork {n : ℕ} (request : Request n) (rich : Bool)
    (index : List Bool) : (Option Bool × Trace) × ℕ :=
  let capacity := BinaryWordObjectArrayAccess.getWithTrace request.physical.lengthStore index
  let resource := BinaryWordObjectArrayAccess.getWithTrace (resourceStore request rich) index
  match capacity.1,resource.1 with
  | some cap,some bid =>
      ((some ((!BinaryRationalArithmetic.lessEqual bid BinaryRationalOpcode.zero) &&
        (!BinaryRationalArithmetic.lessEqual cap bid)),
          wrap 16 2 [capacity.2,resource.2]),
        BinaryRationalArithmetic.lessEqualWork bid BinaryRationalOpcode.zero+
          BinaryRationalArithmetic.lessEqualWork cap bid)
  | _,_ => ((none,wrap 16 2 [capacity.2,resource.2]),0)

theorem fractionalWithWork_erases {n : ℕ} (request : Request n)
    (rich : Bool) (index : List Bool) :
    (fractionalWithWork request rich index).1 =
      fractionalWithTrace request rich index := by
  unfold fractionalWithWork fractionalWithTrace
  cases hCapacity : (BinaryWordObjectArrayAccess.getWithTrace
    request.physical.lengthStore index).1 <;>
  cases hResource : (BinaryWordObjectArrayAccess.getWithTrace
    (resourceStore request rich) index).1 <;>
  simp only [hCapacity,hResource]

theorem fractionalWithWork_cost (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (rich : Bool) (index : List Bool) (j : Fin parsed.1.1)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (fractionalWithWork parsed.1.2 rich index).2 =
      (BinaryGeneralResourceExecution.fractionalWithCharge
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource j).2.booleanWork := by
  have hReads := returned_resource_reads frame parsed hParsed rich index j hIndex
  simp only [fractionalWithWork,resourceStore,hReads.1,hReads.2,
    BinaryGeneralResourceExecution.fractionalWithCharge]

def scanWithWork {n : ℕ} (request : Request n) (rich : Bool) :
    List (Fin n) → List (List Bool) → (Option (List (Fin n)) × Trace) × ℕ
  | [],[] => ((some [],wrap 8 1 []),0)
  | j::rest,index::indices =>
      let current := fractionalWithWork request rich index
      let later := scanWithWork request rich rest indices
      ((match current.1.1,later.1.1 with
        | some keep,some active => some (if keep then j::active else active)
        | _,_ => none,
        wrapList 1 16 2 [current.1.2,later.1.2]),current.2+later.2)
  | _,_ => ((none,wrap 8 1 []),0)

theorem scanWithWork_erases {n : ℕ} (request : Request n) (rich : Bool)
    (items : List (Fin n)) (indices : List (List Bool)) :
    (scanWithWork request rich items indices).1 =
      scanWithTrace request rich items indices := by
  induction items generalizing indices with
  | nil => cases indices <;> rfl
  | cons j rest ih =>
      cases indices with
      | nil => rfl
      | cons index tail =>
          simp only [scanWithWork,scanWithTrace]
          rw [fractionalWithWork_erases,ih]
          rfl

theorem scanWithWork_cost (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (rich : Bool) (items : List (Fin parsed.1.1))
    (indices : List (List Bool))
    (hValues : indices.map BinaryBigEndian.littleValue = items.map Fin.val) :
    (scanWithWork parsed.1.2 rich items indices).2 =
      (BinaryGeneralResourceExecution.scanWithCharge
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        items).2.booleanWork := by
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
          have hc := fractionalWithWork_cost frame parsed hParsed rich index j hHead
          have ht := ih tail hTail
          simp only [scanWithWork,BinaryGeneralResourceExecution.scanWithCharge,
            BinaryGeneralResourceExecution.Charge.add]
          rw [hc,ht]
          rfl

def initialScanWithWork {n : ℕ} (request : Request n) (rich : Bool) :
    (Option (List (Fin n)) × Trace) × ℕ :=
  let indices := BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)
  let scan := scanWithWork request rich (List.finRange n) indices.1
  ((scan.1.1,wrap 32 2 [indices.2,scan.1.2]),scan.2)

theorem initialScanWithWork_erases {n : ℕ} (request : Request n)
    (rich : Bool) :
    (initialScanWithWork request rich).1 = initialScanWithTrace request rich := by
  unfold initialScanWithWork initialScanWithTrace
  dsimp only
  rw [scanWithWork_erases]

theorem initialScanWithWork_cost (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (initialScanWithWork parsed.1.2 rich).2 =
      (BinaryGeneralResourceExecution.initialWithCharge
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2).2.booleanWork := by
  have hAlignment :
      ((BooleanArrayIndexEnumeration.enumerateWithTrace
        (List.finRange parsed.1.1)).1.map BinaryBigEndian.littleValue) =
          (List.finRange parsed.1.1).map Fin.val := by
    rw [finRange_values]
    change List.map BinaryCarryCounter.value _ = _
    simpa only [List.length_finRange] using
      BooleanArrayIndexEnumeration.enumerate_values (List.finRange parsed.1.1)
  have hScan := scanWithWork_cost frame parsed hParsed rich
    (List.finRange parsed.1.1)
    (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange parsed.1.1)).1
    hAlignment
  unfold initialScanWithWork BinaryGeneralResourceExecution.initialWithCharge
  dsimp only
  rw [hScan]
  rfl

theorem initialScanWithWork_raw_boolean_bound (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (initialScanWithWork parsed.1.2 rich).2 ≤
      parsed.1.1*(1000*(9*frame.length+23)^2) := by
  have hRefines := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  rw [hParsed] at hRefines
  have hNative : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hRefines.symm
  have hTables := PRGPhysicalArrayInterface.table_word_width frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hNative
  have hLengths : ∀ j,
      BinaryRationalNormalization.width
        (parsed.1.2.logical.request.prepared.lengths.read j) ≤ 9*frame.length+22 :=
    hTables _ (by
      exact List.Mem.tail _ (List.Mem.head _))
  have hPoor : ∀ j,
      BinaryRationalNormalization.width
        (parsed.1.2.logical.request.prepared.poorResources.read j) ≤ 9*frame.length+22 :=
    hTables _ (by
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hCapacity : ∀ j,
      BinaryRationalNormalization.width
        ((BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length.read j) ≤
        9*frame.length+22 := by
    cases rich with
    | false => simpa [BinaryPRGResourceWork.resourceInput,
        BinaryPRGPreparation.Prepared.poor] using hLengths
    | true => simpa [BinaryPRGResourceWork.resourceInput,
        BinaryPRGPreparation.Prepared.rich] using hLengths
  have hResource : ∀ j,
      BinaryRationalNormalization.width
        ((BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource.read j) ≤
        9*frame.length+22 := by
    cases rich with
    | false => simpa [BinaryPRGResourceWork.resourceInput,
        BinaryPRGPreparation.Prepared.poor] using hPoor
    | true => simpa [BinaryPRGResourceWork.resourceInput,
        BinaryPRGPreparation.Prepared.rich] using hLengths
  have hScan := BinaryGeneralResourceExecution.scanWithCharge_bound
    (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
    (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
    (List.finRange parsed.1.1) (9*frame.length+22) (by omega) hCapacity hResource
  rw [initialScanWithWork_cost frame parsed hParsed rich]
  change (BinaryGeneralResourceExecution.scanWithCharge
    (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
    (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
    (List.finRange parsed.1.1)).2.booleanWork ≤ _
  simpa only [List.length_finRange] using hScan.1

theorem initialScanWithWork_polynomial_boolean_bound (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (initialScanWithWork parsed.1.2 rich).2 ≤
      100000*(frame.length+3)^3 := by
  have hRaw := initialScanWithWork_raw_boolean_bound frame parsed hParsed rich
  have hRefines := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  rw [hParsed] at hRefines
  have hNative : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hRefines.symm
  have hn := PRGNativeArrayControl.dimension_bound frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hNative
  change parsed.1.1 ≤ frame.length at hn
  let x := frame.length+3
  have hN : parsed.1.1 ≤ x := by dsimp [x]; omega
  have hW : 9*frame.length+23 ≤ 9*x := by dsimp [x]; omega
  have hSquare : (9*frame.length+23)^2 ≤ (9*x)^2 := Nat.pow_le_pow_left hW 2
  have hProduct : parsed.1.1*(1000*(9*frame.length+23)^2) ≤
      x*(1000*(9*x)^2) := Nat.mul_le_mul hN (Nat.mul_le_mul_left 1000 hSquare)
  have hExpand : x*(1000*(9*x)^2) = 81000*x^3 := by ring
  change (initialScanWithWork parsed.1.2 rich).2 ≤ 100000*x^3
  omega

theorem initialScanWithWork_polynomial_trace_usage (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    usage (initialScanWithWork parsed.1.2 rich).1.2 ≤
      2000000000*(frame.length+3)^7 := by
  rw [initialScanWithWork_erases]
  exact BinaryPRGPhysicalResourceRawBound.initialScanWithTrace_polynomial_usage
    frame parsed hParsed rich

def initialStateWithWork (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (_hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (BinaryResourceState.State parsed.1.1 × Trace) × ℕ :=
  let scan := initialScanWithWork parsed.1.2 rich
  ((⟨(BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource,
      scan.1.1.getD []⟩,scan.1.2),scan.2)

theorem initialStateWithWork_erases (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (initialStateWithWork frame parsed hParsed rich).1 =
      initialStateWithPhysical frame parsed hParsed rich := by
  unfold initialStateWithWork initialStateWithPhysical
  dsimp only
  rw [initialScanWithWork_erases]

def initialCertifiedWithWork (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length × Trace) × ℕ :=
  let input := BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich
  let canonical := BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich
  let native := BinaryResourcePair.initial input.length input.resource canonical.2.1 canonical.2.2
  let physical := initialStateWithWork frame parsed hParsed rich
  have hState : physical.1.1 = native.state := by
    rw [initialStateWithWork_erases]
    exact initialStateWithPhysical_state frame parsed hParsed rich
  ((⟨physical.1.1,
    (by rw [hState]; exact native.canonical),
    (by rw [hState]; exact native.nodup),
    (by rw [hState]; exact native.membership)⟩,physical.1.2),physical.2)

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

theorem initialCertifiedWithWork_state (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool) :
    (initialCertifiedWithWork frame parsed hParsed rich).1.1 =
      BinaryResourcePair.initial
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length
        (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).resource
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1
        (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.2 := by
  apply certified_eq_of_state
  change (initialStateWithWork frame parsed hParsed rich).1.1 = _
  exact (congrArg Prod.fst (initialStateWithWork_erases frame parsed hParsed rich)).trans
    (initialStateWithPhysical_state frame parsed hParsed rich)

def resourceWorkWithPhysicalComparison (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (((Option (BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length) × ℕ) ×
      BinaryGeneralResourceExecution.Charge) × Trace) × ℕ :=
  let initial := initialCertifiedWithWork frame parsed hParsed rich
  let later := BinaryGeneralResourceRunWork.run
    (BinaryPRGResourceWork.resource_canonical parsed.1.2.logical.request rich).2.1 N initial.1.1 bits
  ((later,initial.1.2),initial.2)

theorem resourceWorkWithPhysicalComparison_state (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).1.1.1 =
      (BinaryPRGResourceWork.resourceWork parsed.1.2.logical.request rich N bits).1 := by
  unfold resourceWorkWithPhysicalComparison BinaryPRGResourceWork.resourceWork
    BinaryGeneralResourceRunWork.initialRun
  dsimp only
  rw [initialCertifiedWithWork_state]
  rw [BinaryGeneralResourceExecution.initialWithCharge_state]

theorem resourceWorkWithPhysicalComparison_trace (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).1.2 =
      (initialScanWithWork parsed.1.2 rich).1.2 := by
  rfl

theorem resourceWorkWithPhysicalComparison_cost (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).2 =
      (initialScanWithWork parsed.1.2 rich).2 := by
  rfl

theorem resourceWorkWithPhysicalComparison_boolean_eq (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).2 +
      (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).1.1.2.booleanWork =
      (BinaryPRGResourceWork.resourceWork parsed.1.2.logical.request rich N bits).2.booleanWork := by
  rw [resourceWorkWithPhysicalComparison_cost frame parsed hParsed rich N bits,
    initialScanWithWork_cost frame parsed hParsed rich]
  unfold resourceWorkWithPhysicalComparison BinaryPRGResourceWork.resourceWork
    BinaryGeneralResourceRunWork.initialRun
  dsimp only
  rw [initialCertifiedWithWork_state]
  rw [BinaryGeneralResourceExecution.initialWithCharge_state]
  rfl

theorem resourceWorkWithPhysicalComparison_boolean_bound (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).2 +
      (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).1.1.2.booleanWork ≤
      7100000 * parsed.1.1 *
        (parsed.1.2.logical.request.source.originalInputWordWidth + 2) ^ 3 +
      52 * N * (parsed.1.2.logical.request.source.originalInputWordWidth + 2) := by
  rw [resourceWorkWithPhysicalComparison_boolean_eq]
  exact BinaryPRGResourceWork.resource_boolean_bound
    parsed.1.2.logical.request rich N bits

theorem resourceWorkWithPhysicalComparison_raw_boolean_bound (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).2 +
      (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).1.1.2.booleanWork ≤
      7100000 * parsed.1.1 *
        ((frame.length+2)*(4*frame.length+13)+2)^3 +
      52 * N * ((frame.length+2)*(4*frame.length+13)+2) := by
  have hPhysical := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hPhysical
  have hAccuracy : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hPhysical.symm
  have hOriginal := BinaryPRGAccuracyRulerRequest.read_state frame
  rw [hAccuracy] at hOriginal
  have hRead : BinaryPRGRequest.read frame =
      some (⟨parsed.1.1,parsed.1.2.logical.request⟩,parsed.2) := by
    simpa only [Option.map_some,BinaryPRGAccuracyRulerRequest.forget,
      BinaryPRGPhysicalRawRequestLifetime.forgetParsed] using hOriginal.symm
  rw [resourceWorkWithPhysicalComparison_boolean_eq]
  exact BinaryPRGResourceWork.parsed_resource_boolean_bound
    frame parsed.2 parsed.1.2.logical.request hRead rich N bits

theorem resourceWorkWithPhysicalComparison_polynomial_trace_usage (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) :
    usage (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).1.2 ≤
      2000000000*(frame.length+3)^7 := by
  rw [resourceWorkWithPhysicalComparison_trace]
  exact initialScanWithWork_polynomial_trace_usage frame parsed hParsed rich

theorem resourceWorkWithPhysicalComparison_polynomial_trace_prefix (frame : List Bool)
    (parsed : (Σ n, Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed
        (resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).1.2 steps ≤
        borrowed+2000000000*(frame.length+3)^7 ∧
      framePeak
        ((resourceWorkWithPhysicalComparison frame parsed hParsed rich N bits).1.2.take steps) ≤
        2000000000*(frame.length+3)^7 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (resourceWorkWithPhysicalComparison_polynomial_trace_usage frame parsed hParsed rich N bits)
    borrowed steps

end Blotto.BinaryPRGPhysicalResourceComparisonWork
