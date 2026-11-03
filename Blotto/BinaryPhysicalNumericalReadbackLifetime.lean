import Blotto.BinaryPRGPhysicalResourceRawBound
import Blotto.BinaryPRGWordControllerBooleanResourceSource

/-! Complete physical numerical-table readback through the returned pointer
slots and object heap. Boolean carry indices, rather than native array reads,
select every entry. The resulting word lists are a conversion boundary for
the seeded resource-loop tree initializer; the tree join remains separate. -/
namespace Blotto.BinaryPhysicalNumericalReadbackLifetime
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime
set_option autoImplicit false
set_option maxHeartbeats 3000000

def readManyWithTraceAndWork {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    List (List Bool) → (Option (List SignedWord) × Trace) × ℕ
  | [] => ((some [],wrap 8 1 []),1)
  | index::rest =>
      let current := BinaryWordObjectArrayAccess.getWithTrace store index
      let later := readManyWithTraceAndWork store rest
      let result := match current.1,later.1.1 with
        | some word,some words => some (word::words)
        | _,_ => none
      ((result,wrapList 1 16 2 [current.2,later.1.2]),later.2+1)

def readManyWithTrace {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (indices : List (List Bool)) : Option (List SignedWord) × Trace :=
  (readManyWithTraceAndWork store indices).1

theorem readManyWithTraceAndWork_charge {n : ℕ}
    (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) :
    (readManyWithTraceAndWork store indices).2 = indices.length+1 := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [readManyWithTraceAndWork,List.length_cons,ih]

theorem readMany_aligned {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (table : FixedArrayTable n SignedWord)
    (items : List (Fin n)) (indices : List (List Bool))
    (hValues : indices.map BinaryBigEndian.littleValue = items.map Fin.val)
    (hRead : ∀ index j,
      BinaryBigEndian.littleValue index = j.val →
      (BinaryWordObjectArrayAccess.getWithTrace store index).1 =
        some (table.read j)) :
    (readManyWithTrace store indices).1 = some (items.map table.read) := by
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
          have hc := hRead index j hHead
          have ht := ih tail hTail
          change (readManyWithTraceAndWork store tail).1.1 = _ at ht
          simp only [readManyWithTrace,readManyWithTraceAndWork,hc,ht,List.map_cons]

def readAllWithTraceAndWork {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    (Option (List SignedWord) × Trace) × ℕ :=
  let indices := BooleanArrayIndexEnumeration.enumerateWithTrace
    (List.finRange n)
  let result := readManyWithTraceAndWork store indices.1
  ((result.1.1,wrap 32 2 [indices.2,result.1.2]),result.2+1)

def readAllWithTrace {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    Option (List SignedWord) × Trace :=
  (readAllWithTraceAndWork store).1

theorem readAllWithTraceAndWork_charge {n : ℕ}
    (store : BinaryWordObjectArray.Store n) :
    (readAllWithTraceAndWork store).2 = n+2 := by
  have hLength :
      (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1.length = n := by
    have h := congrArg List.length
      (BooleanArrayIndexEnumeration.enumerate_values (List.finRange n))
    simpa only [List.length_map,List.length_range,List.length_finRange] using h
  unfold readAllWithTraceAndWork
  dsimp only
  rw [readManyWithTraceAndWork_charge,hLength]

theorem readAll_state {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (table : FixedArrayTable n SignedWord)
    (hRead : ∀ index j,
      BinaryBigEndian.littleValue index = j.val →
      (BinaryWordObjectArrayAccess.getWithTrace store index).1 =
        some (table.read j)) :
    (readAllWithTrace store).1 = some table.data.toList := by
  have hValues :
      ((BooleanArrayIndexEnumeration.enumerateWithTrace
        (List.finRange n)).1.map BinaryBigEndian.littleValue) =
          (List.finRange n).map Fin.val := by
    rw [BinaryPRGPhysicalResourceInitialLifetime.finRange_values]
    change List.map BinaryCarryCounter.value _ = _
    simpa only [List.length_finRange] using
      BooleanArrayIndexEnumeration.enumerate_values (List.finRange n)
  have h := readMany_aligned store table (List.finRange n)
    (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1
    hValues hRead
  unfold readAllWithTrace readAllWithTraceAndWork
  dsimp only
  change (readManyWithTraceAndWork store
    (BooleanArrayIndexEnumeration.enumerateWithTrace (List.finRange n)).1).1.1 = _ at h
  rw [h,← List.ofFn_eq_map,
    BinaryPRGWordControllerBooleanResourceSource.arrayWords]

def readBudget {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (indices : List (List Bool)) : ℕ :=
  (indices.map (fun index =>
    BinaryWordObjectArrayAccess.envelope store index.length)).sum+
      32*(indices.length+1)

theorem readMany_usage {n : ℕ} (store : BinaryWordObjectArray.Store n)
    (indices : List (List Bool)) :
    usage (readManyWithTrace store indices).2 ≤
      readBudget store indices := by
  induction indices with
  | nil =>
      have hw := wrap_usage 8 1 ([] : List Trace)
      simp only [List.map_nil,List.sum_nil] at hw
      change usage (wrap 8 1 []) ≤ _
      unfold readBudget
      simp only [List.map_nil,List.sum_nil,List.length_nil]
      omega
  | cons index rest ih =>
      have hc := BinaryWordObjectArrayAccess.get_usage store index
      have hw := wrapList_usage 1 16 2
        [(BinaryWordObjectArrayAccess.getWithTrace store index).2,
          (readManyWithTrace store rest).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (readManyWithTrace store (index::rest)).2 ≤ _ at hw
      unfold readBudget at *
      simp only [List.map_cons,List.sum_cons,List.length_cons] at *
      omega

private theorem sum_read_budget {n : ℕ}
    (store : BinaryWordObjectArray.Store n)
    (indices : List (List Bool)) (width : ℕ)
    (h : ∀ index ∈ indices,index.length ≤ width) :
    (indices.map (fun index =>
      BinaryWordObjectArrayAccess.envelope store index.length)).sum ≤
        indices.length*BinaryWordObjectArrayAccess.envelope store width := by
  induction indices with
  | nil => simp
  | cons index rest ih =>
      have hc := BinaryPRGPhysicalResourceInitialLifetime.readEnvelope_mono
        store (h index (by simp))
      have ht := ih (by intro word hw; exact h word (by simp [hw]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

/-- Proof-side native lookup charge for the same Boolean indices visited by
`readManyWithTraceAndWork`. This is a companion cost certificate; the selected
reader executes `getWithTrace` and does not evaluate this definition. -/
def nativeLookupWork {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    List (List Bool) → ℕ
  | [] => 0
  | index::rest =>
      (BinaryWordObjectArray.getWithWork store index).2 + nativeLookupWork store rest

def nativeReadManyWithWork {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    List (List Bool) → Option (List SignedWord) × ℕ
  | [] => (some [],0)
  | index::rest =>
      let current := BinaryWordObjectArray.getWithWork store index
      let later := nativeReadManyWithWork store rest
      let result := match current.1,later.1 with
        | some word,some words => some (word::words)
        | _,_ => none
      (result,current.2+later.2)

theorem nativeReadManyWithWork_charge {n : ℕ}
    (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) :
    (nativeReadManyWithWork store indices).2 =
      nativeLookupWork store indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [nativeReadManyWithWork,nativeLookupWork,ih]

theorem readManyWithTraceAndWork_native_state {n : ℕ}
    (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) :
    (readManyWithTraceAndWork store indices).1.1 =
      (nativeReadManyWithWork store indices).1 := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [readManyWithTraceAndWork,nativeReadManyWithWork,
        BinaryWordObjectArrayAccess.get_state,ih]

theorem nativeLookupWork_envelope {n : ℕ}
    (store : BinaryWordObjectArray.Store n) (indices : List (List Bool)) :
    nativeLookupWork store indices ≤
      (indices.map (fun index =>
        BinaryWordObjectArrayAccess.envelope store index.length)).sum := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      have hc := BinaryWordObjectArrayAccess.native_lookup_work_le_envelope
        store index
      simp only [nativeLookupWork,List.map_cons,List.sum_cons]
      omega

def pairNativeLookupWork {n : ℕ} (request : Request n) : ℕ :=
  let indices := (BooleanArrayIndexEnumeration.enumerateWithTrace
    (List.finRange n)).1
  nativeLookupWork request.physical.lengthStore indices +
    nativeLookupWork request.physical.poorStore indices

theorem pairNativeLookupWork_bound {n : ℕ} (request : Request n) :
    pairNativeLookupWork request ≤
      n * (BinaryWordObjectArrayAccess.envelope
        request.physical.lengthStore (binaryWordWidth n) +
        BinaryWordObjectArrayAccess.envelope
          request.physical.poorStore (binaryWordWidth n)) := by
  let indices := (BooleanArrayIndexEnumeration.enumerateWithTrace
    (List.finRange n)).1
  have hWidth : ∀ index ∈ indices,
      index.length ≤ binaryWordWidth n := by
    intro index hi
    simpa only [List.length_finRange] using
      BooleanArrayIndexEnumeration.enumerate_width
        (List.finRange n) index hi
  have hLength : indices.length = n := by
    have h := congrArg List.length
      (BooleanArrayIndexEnumeration.enumerate_values (List.finRange n))
    simpa only [List.length_map,List.length_range,List.length_finRange] using h
  have hl := nativeLookupWork_envelope request.physical.lengthStore indices
  have hp := nativeLookupWork_envelope request.physical.poorStore indices
  have hsl := sum_read_budget request.physical.lengthStore indices
    (binaryWordWidth n) hWidth
  have hsp := sum_read_budget request.physical.poorStore indices
    (binaryWordWidth n) hWidth
  rw [hLength] at hsl hsp
  unfold pairNativeLookupWork
  dsimp only
  change nativeLookupWork request.physical.lengthStore indices +
    nativeLookupWork request.physical.poorStore indices ≤ _
  simp only [Nat.mul_add]
  omega

/-- A length-based allowance for the native cost of the selected two-table
physical lookup route. Computing this expression does not rerun either lookup. -/
def pairLookupAllowance {n : ℕ} (request : Request n) : ℕ :=
  n * (BinaryWordObjectArrayAccess.envelope
    request.physical.lengthStore (binaryWordWidth n) +
    BinaryWordObjectArrayAccess.envelope
      request.physical.poorStore (binaryWordWidth n))

theorem pairNativeLookupWork_le_allowance {n : ℕ} (request : Request n) :
    pairNativeLookupWork request ≤ pairLookupAllowance request :=
  pairNativeLookupWork_bound request

theorem readAll_usage {n : ℕ} (store : BinaryWordObjectArray.Store n) :
    usage (readAllWithTrace store).2 ≤
      n*BinaryWordObjectArrayAccess.envelope store (binaryWordWidth n)+
        64*n+88 := by
  let indices := (BooleanArrayIndexEnumeration.enumerateWithTrace
    (List.finRange n)).1
  have hIndices := BooleanArrayIndexEnumeration.enumerate_usage
    (List.finRange n)
  have hRead := readMany_usage store indices
  have hWidth : ∀ index ∈ indices,
      index.length ≤ binaryWordWidth n := by
    intro index hi
    simpa only [List.length_finRange] using
      BooleanArrayIndexEnumeration.enumerate_width
        (List.finRange n) index hi
  have hLength : indices.length = n := by
    have h := congrArg List.length
      (BooleanArrayIndexEnumeration.enumerate_values
        (List.finRange n))
    simpa only [List.length_map,List.length_range,List.length_finRange] using h
  have hSum := sum_read_budget store indices (binaryWordWidth n) hWidth
  have hw := wrap_usage 32 2
    [(BooleanArrayIndexEnumeration.enumerateWithTrace
      (List.finRange n)).2,(readManyWithTrace store indices).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (readAllWithTrace store).2 ≤ _ at hw
  unfold readBudget at hRead
  simp only [List.length_finRange] at hIndices
  rw [hLength] at hRead hSum
  omega

theorem accepted_length_words (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    (readAllWithTrace parsed.1.2.physical.lengthStore).1 =
      some parsed.1.2.logical.request.prepared.lengths.data.toList := by
  apply readAll_state
  intro index j hIndex
  exact (returned_stores_readback frame parsed hParsed index j hIndex).1

theorem accepted_poor_words (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    (readAllWithTrace parsed.1.2.physical.poorStore).1 =
      some parsed.1.2.logical.request.prepared.poorResources.data.toList := by
  apply readAll_state
  intro index j hIndex
  exact (returned_stores_readback frame parsed hParsed index j hIndex).2

theorem request_length_words {n : ℕ} (request : Request n) :
    (readAllWithTrace request.physical.lengthStore).1 =
      some request.logical.request.prepared.lengths.data.toList := by
  apply readAll_state
  intro index j hIndex
  rw [request.numerical_eq]
  exact (request.physical.readback index j hIndex).1

theorem request_poor_words {n : ℕ} (request : Request n) :
    (readAllWithTrace request.physical.poorStore).1 =
      some request.logical.request.prepared.poorResources.data.toList := by
  apply readAll_state
  intro index j hIndex
  rw [request.numerical_eq]
  exact (request.physical.readback index j hIndex).2

set_option maxHeartbeats 200000

/-- Reify both numerical tables from the physical stores. Both readback traces
are retained, including the Boolean-carry index enumeration. -/
def readPairWithTraceAndWork {n : ℕ} (request : Request n) :
    (Option (List SignedWord × List SignedWord) × Trace) × ℕ :=
  let lengths := readAllWithTraceAndWork request.physical.lengthStore
  let poor := readAllWithTraceAndWork request.physical.poorStore
  let result := do
    let lengthWords ← lengths.1.1
    let poorWords ← poor.1.1
    pure (lengthWords,poorWords)
  ((result,wrap 32 2 [lengths.1.2,poor.1.2]),lengths.2+poor.2+1)

def readPairWithTrace {n : ℕ} (request : Request n) :
    Option (List SignedWord × List SignedWord) × Trace :=
  (readPairWithTraceAndWork request).1

theorem readPairWithTraceAndWork_charge {n : ℕ} (request : Request n) :
    (readPairWithTraceAndWork request).2 = 2*n+5 := by
  unfold readPairWithTraceAndWork
  dsimp only
  rw [readAllWithTraceAndWork_charge,readAllWithTraceAndWork_charge]
  omega

theorem readPairWithTraceAndWork_erases {n : ℕ} (request : Request n) :
    (readPairWithTraceAndWork request).1 = readPairWithTrace request := rfl

theorem accepted_pair_words (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    (readPairWithTrace parsed.1.2).1 = some
      (parsed.1.2.logical.request.prepared.lengths.data.toList,
        parsed.1.2.logical.request.prepared.poorResources.data.toList) := by
  have hl := accepted_length_words frame parsed hParsed
  have hp := accepted_poor_words frame parsed hParsed
  change (readAllWithTraceAndWork parsed.1.2.physical.lengthStore).1.1 = _ at hl
  change (readAllWithTraceAndWork parsed.1.2.physical.poorStore).1.1 = _ at hp
  simp [readPairWithTrace,readPairWithTraceAndWork,hl,hp]

theorem request_pair_words {n : ℕ} (request : Request n) :
    (readPairWithTrace request).1 = some
      (request.logical.request.prepared.lengths.data.toList,
        request.logical.request.prepared.poorResources.data.toList) := by
  have hl := request_length_words request
  have hp := request_poor_words request
  change (readAllWithTraceAndWork request.physical.lengthStore).1.1 = _ at hl
  change (readAllWithTraceAndWork request.physical.poorStore).1.1 = _ at hp
  simp [readPairWithTrace,readPairWithTraceAndWork,hl,hp]

/-- A computable width ceiling from the two retained physical object tapes.
It does not inspect the logical request or re-run the indexed readback. -/
def physicalWordWidth {n : ℕ} (request : Request n) : ℕ :=
  max 1 (max request.physical.lengthStore.heap.tape.length
    request.physical.poorStore.heap.tape.length)

theorem physicalWordWidth_pos {n : ℕ} (request : Request n) :
    1 ≤ physicalWordWidth request := by
  unfold physicalWordWidth
  exact Nat.le_max_left _ _

theorem physicalWordWidth_inputs {n : ℕ} (request : Request n) :
    (∀ j,width (request.logical.request.prepared.lengths.read j) ≤
      physicalWordWidth request) ∧
    (∀ j,width (request.logical.request.prepared.poorResources.read j) ≤
      physicalWordWidth request) := by
  constructor
  · intro j
    let index := BinaryCarryCounter.count (List.finRange j.val) []
    have hIndex : BinaryBigEndian.littleValue index = j.val := by
      change BinaryCarryCounter.value (BinaryCarryCounter.count
        (List.finRange j.val) []) = j.val
      rw [BinaryCarryCounter.count_value]
      simp
      rfl
    have hRead := (request.physical.readback index j hIndex).1
    have hWidth := BinaryWordObjectArrayAccess.get_width_le_tape
      request.physical.lengthStore index
      (request.physical.numerical.lengths.read j) hRead
    rw [← request.numerical_eq] at hWidth
    exact hWidth.trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  · intro j
    let index := BinaryCarryCounter.count (List.finRange j.val) []
    have hIndex : BinaryBigEndian.littleValue index = j.val := by
      change BinaryCarryCounter.value (BinaryCarryCounter.count
        (List.finRange j.val) []) = j.val
      rw [BinaryCarryCounter.count_value]
      simp
      rfl
    have hRead := (request.physical.readback index j hIndex).2
    have hWidth := BinaryWordObjectArrayAccess.get_width_le_tape
      request.physical.poorStore index
      (request.physical.numerical.poorResources.read j) hRead
    rw [← request.numerical_eq] at hWidth
    exact hWidth.trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem accepted_physicalWordWidth_bound (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    physicalWordWidth parsed.1.2 ≤
      PRGPhysicalArrayInterface.heapCap frame.length+1 := by
  have hCaps := BinaryPRGPhysicalResourceRawBound.returned_raw_caps
    frame parsed hParsed
  unfold physicalWordWidth
  omega

def pairEnvelope {n : ℕ} (request : Request n) : ℕ :=
  n*(BinaryWordObjectArrayAccess.envelope request.physical.lengthStore (binaryWordWidth n)+
    BinaryWordObjectArrayAccess.envelope request.physical.poorStore (binaryWordWidth n))+
    128*n+214

theorem readPair_usage {n : ℕ} (request : Request n) :
    usage (readPairWithTrace request).2 ≤ pairEnvelope request := by
  have hl := readAll_usage request.physical.lengthStore
  have hp := readAll_usage request.physical.poorStore
  have hw := wrap_usage 32 2
    [(readAllWithTrace request.physical.lengthStore).2,
      (readAllWithTrace request.physical.poorStore).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (readPairWithTrace request).2 ≤ _ at hw
  unfold pairEnvelope
  simp only [Nat.mul_add]
  omega

theorem accepted_dimension (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    parsed.1.1 ≤ frame.length := by
  have hOld := readWithTrace_original frame
  rw [hParsed] at hOld
  have hRead : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  exact BinaryPRGSeedRequestBound.read_dimension_bound frame
    (forgetParsed parsed) hRead

theorem accepted_pair_control_work (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    (readPairWithTraceAndWork parsed.1.2).2 ≤ 2*frame.length+5 := by
  rw [readPairWithTraceAndWork_charge]
  have hDimension := accepted_dimension frame parsed hParsed
  omega

theorem accepted_pair_raw_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    usage (readPairWithTrace parsed.1.2).2 ≤
      BinaryPRGPhysicalResourceRawBound.rawScanEnvelope frame.length+
        64*frame.length+126 := by
  have hn := accepted_dimension frame parsed hParsed
  have hLookup := BinaryPRGPhysicalResourceRawBound.returned_lookupEnvelope_raw
    frame parsed hParsed false
  unfold BinaryPRGPhysicalResourceInitialLifetime.lookupEnvelope
    BinaryPRGPhysicalResourceInitialLifetime.resourceStore at hLookup
  simp only [Bool.false_eq_true,ite_false] at hLookup
  have hProduct : parsed.1.1 *
      (BinaryWordObjectArrayAccess.envelope parsed.1.2.physical.lengthStore
        (binaryWordWidth parsed.1.1)+
        BinaryWordObjectArrayAccess.envelope parsed.1.2.physical.poorStore
          (binaryWordWidth parsed.1.1)) ≤
      frame.length*(2*PRGPhysicalArrayInterface.readEnvelope frame.length+24) := by
    apply Nat.mul_le_mul hn
    omega
  have hUsage := readPair_usage parsed.1.2
  unfold pairEnvelope at hUsage
  unfold BinaryPRGPhysicalResourceRawBound.rawScanEnvelope
  omega

theorem accepted_pair_native_lookup_work (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    pairNativeLookupWork parsed.1.2 ≤
      BinaryPRGPhysicalResourceRawBound.rawScanEnvelope frame.length := by
  have hn := accepted_dimension frame parsed hParsed
  have hLookup := BinaryPRGPhysicalResourceRawBound.returned_lookupEnvelope_raw
    frame parsed hParsed false
  unfold BinaryPRGPhysicalResourceInitialLifetime.lookupEnvelope
    BinaryPRGPhysicalResourceInitialLifetime.resourceStore at hLookup
  simp only [Bool.false_eq_true,ite_false] at hLookup
  have hProduct : parsed.1.1 *
      (BinaryWordObjectArrayAccess.envelope parsed.1.2.physical.lengthStore
        (binaryWordWidth parsed.1.1)+
        BinaryWordObjectArrayAccess.envelope parsed.1.2.physical.poorStore
          (binaryWordWidth parsed.1.1)) ≤
      frame.length*(2*PRGPhysicalArrayInterface.readEnvelope frame.length+24) := by
    apply Nat.mul_le_mul hn
    omega
  have hNative := pairNativeLookupWork_bound parsed.1.2
  unfold BinaryPRGPhysicalResourceRawBound.rawScanEnvelope
  omega

theorem accepted_pair_lookup_allowance (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    pairLookupAllowance parsed.1.2 ≤
      BinaryPRGPhysicalResourceRawBound.rawScanEnvelope frame.length := by
  have hn := accepted_dimension frame parsed hParsed
  have hLookup := BinaryPRGPhysicalResourceRawBound.returned_lookupEnvelope_raw
    frame parsed hParsed false
  unfold BinaryPRGPhysicalResourceInitialLifetime.lookupEnvelope
    BinaryPRGPhysicalResourceInitialLifetime.resourceStore at hLookup
  simp only [Bool.false_eq_true,ite_false] at hLookup
  have hProduct : parsed.1.1 *
      (BinaryWordObjectArrayAccess.envelope parsed.1.2.physical.lengthStore
        (binaryWordWidth parsed.1.1)+
        BinaryWordObjectArrayAccess.envelope parsed.1.2.physical.poorStore
          (binaryWordWidth parsed.1.1)) ≤
      frame.length*(2*PRGPhysicalArrayInterface.readEnvelope frame.length+24) := by
    apply Nat.mul_le_mul hn
    omega
  unfold pairLookupAllowance BinaryPRGPhysicalResourceRawBound.rawScanEnvelope
  omega

theorem accepted_pair_lookup_allowance_polynomial (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    pairLookupAllowance parsed.1.2 ≤
      2000000000*(frame.length+3)^7 :=
  (accepted_pair_lookup_allowance frame parsed hParsed).trans
    (BinaryPRGPhysicalResourceRawBound.rawScanEnvelope_polynomial frame.length)

theorem accepted_pair_native_lookup_polynomial (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    pairNativeLookupWork parsed.1.2 ≤
      2000000000*(frame.length+3)^7 :=
  (accepted_pair_native_lookup_work frame parsed hParsed).trans
    (BinaryPRGPhysicalResourceRawBound.rawScanEnvelope_polynomial frame.length)

theorem accepted_pair_control_and_lookup_polynomial (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    (readPairWithTraceAndWork parsed.1.2).2 +
      pairNativeLookupWork parsed.1.2 ≤
        2000000002*(frame.length+3)^7 := by
  have hc := accepted_pair_control_work frame parsed hParsed
  have hl := accepted_pair_native_lookup_polynomial frame parsed hParsed
  have hx : 1 ≤ frame.length+3 := by omega
  have hPower : frame.length+3 ≤ (frame.length+3)^7 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right hx (show (1:ℕ) ≤ 7 by omega))
  omega

theorem accepted_pair_polynomial_usage (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed) :
    usage (readPairWithTrace parsed.1.2).2 ≤
      2000000200*(frame.length+3)^7 := by
  have hRaw := accepted_pair_raw_usage frame parsed hParsed
  have hPoly := BinaryPRGPhysicalResourceRawBound.rawScanEnvelope_polynomial frame.length
  have hLength : frame.length ≤ (frame.length+3)^7 := by
    have hx : 1 ≤ frame.length+3 := by omega
    have h := Nat.pow_le_pow_right hx (show (1:ℕ) ≤ 7 by omega)
    simp only [pow_one] at h
    exact (by omega : frame.length ≤ frame.length+3).trans h
  have hOne : 1 ≤ (frame.length+3)^7 :=
    Nat.one_le_pow _ _ (by omega)
  omega

theorem accepted_pair_polynomial_prefix (frame : List Bool)
    (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (readWithTrace frame).1 = some parsed)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (readPairWithTrace parsed.1.2).2 steps ≤
        borrowed+2000000200*(frame.length+3)^7 ∧
      framePeak ((readPairWithTrace parsed.1.2).2.take steps) ≤
        2000000200*(frame.length+3)^7 := by
  exact BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_pair_polynomial_usage frame parsed hParsed) borrowed steps

end Blotto.BinaryPhysicalNumericalReadbackLifetime
