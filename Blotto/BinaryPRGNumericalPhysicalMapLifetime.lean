import Blotto.BinaryPRGNumericalPhysicalEntries

/-! The projection that feeds the direct physical numerical array is itself
executed and measured here. Its returned list, rather than a recomputed
`words` projection or a native-array readback, is what the Boolean object
allocator consumes. The map's cons visits/frames and the allocator's trace
are joined; the corresponding counted work path uses the same reached list. -/
namespace Blotto.BinaryPRGNumericalPhysicalMapLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGRecognition
open BinaryPRGPreparation BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGNumericalPhysicalEntries
set_option autoImplicit false
set_option maxHeartbeats 3000000

def prepareWithWork (entries : List (SignedWord × Trace)) :
    BinaryWordObjectArray.Store (BinaryLifetimeArray.mapWithVisits Prod.fst entries).1.length × ℕ :=
  let projected := BinaryLifetimeArray.mapWithVisits Prod.fst entries
  let allocated := BinaryWordObjectArrayLifetime.prepareWithWork projected.1
  (allocated.1,projected.2+allocated.2+8)

def prepareWithTrace (entries : List (SignedWord × Trace)) :
    BinaryWordObjectArray.Store
      (BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries).1.length × Trace :=
  let projected := BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries
  let allocated := BinaryWordObjectArrayLifetime.prepareWithTrace projected.1
  (allocated.1,wrapList 1 32 2 [projected.2,allocated.2])

def preparePairWithTrace (lengthEntries poorEntries : List (SignedWord × Trace)) :=
  (prepareWithTrace lengthEntries,prepareWithTrace poorEntries)

theorem projected_trace_words (entries : List (SignedWord × Trace)) :
    (BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries).1 = words entries :=
  BinaryLifetimeArray.mapDirectWithTrace_state Prod.fst entries

theorem projected_work_words (entries : List (SignedWord × Trace)) :
    (BinaryLifetimeArray.mapWithVisits Prod.fst entries).1 = words entries := by
  rw [BinaryLifetimeArray.mapWithVisits_state]
  exact (BinaryLifetimeArray.mapDirect_eq_map Prod.fst entries).symm

theorem prepareWithTrace_readback (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace (prepareWithTrace entries).1 index).1 =
      some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) := by
  simp only [prepareWithTrace]
  rw [projected_trace_words]
  exact physical_readback n entries hEntries index j hIndex

theorem prepareWithWork_readback (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArray.getWithWork (prepareWithWork entries).1 index).1 =
      some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) := by
  simp only [prepareWithWork,BinaryWordObjectArray.getWithWork_state,
    BinaryWordObjectArrayLifetime.prepareWithWork_state]
  rw [projected_work_words,BinaryWordObjectArray.get_prepare,hIndex]
  have hLen : (words entries).length = n := by rw [words_length,hEntries]
  rw [List.getElem?_eq_getElem (by rw [hLen]; exact j.isLt)]
  congr 1
  rw [BinaryLifetimeArray.fromEntries_read]
  simp [words,BinaryLifetimeArray.mapDirect_eq_map]

theorem projection_usage (entries : List (SignedWord × Trace)) :
    usage (BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries).2 ≤
      2*entries.length+1 := by
  obtain ⟨hc,ha,hf⟩ := BinaryLifetimeArray.mapDirectWithTrace_bounds Prod.fst entries
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

theorem prepareWithTrace_usage (entries : List (SignedWord × Trace)) :
    usage (prepareWithTrace entries).2 ≤
      BinaryWordObjectArrayLifetime.envelope (words entries)+2*entries.length+40 := by
  let projected := BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries
  have hMap : usage projected.2 ≤ 2*entries.length+1 := projection_usage entries
  have hAlloc := BinaryWordObjectArrayLifetime.prepare_usage projected.1
  have hProjected : projected.1 = words entries := projected_trace_words entries
  rw [hProjected] at hAlloc
  have hWrap := wrapList_usage 1 32 2
    [projected.2,(BinaryWordObjectArrayLifetime.prepareWithTrace projected.1).2]
  change usage (prepareWithTrace entries).2 ≤ _ at hWrap
  conv at hWrap => rhs; rw [hProjected]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  omega

theorem prepareWithWork_bound (entries : List (SignedWord × Trace)) :
    (prepareWithWork entries).2 ≤
      BinaryWordObjectArrayLifetime.envelope (words entries)+entries.length+8 := by
  have hVisits := BinaryLifetimeArray.mapWithVisits_visits Prod.fst entries
  have hAlloc := BinaryWordObjectArrayLifetime.prepareWithWork_bound
    (BinaryLifetimeArray.mapWithVisits Prod.fst entries).1
  rw [projected_work_words] at hAlloc
  have hEnvelope := PRGPhysicalArrayInterface.workEnvelope_le_source (words entries)
  change _+_+8 ≤ _
  rw [projected_work_words]
  omega

theorem prepareWithTrace_raw_bound (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22) :
    usage (prepareWithTrace entries).2 ≤
      PRGPhysicalArrayInterface.preparationBound length+2*length+40 := by
  have hAlloc := physical_raw_envelope length n entries hEntries hn hWidth
  have hMap := prepareWithTrace_usage entries
  rw [hEntries] at hMap
  omega

theorem prepareWithWork_raw_bound (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22) :
    (prepareWithWork entries).2 ≤
      PRGPhysicalArrayInterface.preparationBound length+length+8 := by
  have hAlloc := physical_raw_envelope length n entries hEntries hn hWidth
  have hMap := prepareWithWork_bound entries
  rw [hEntries] at hMap
  omega

theorem prepareWithTrace_raw_prefix (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace entries).2 steps ≤
        borrowed+PRGPhysicalArrayInterface.preparationBound length+2*length+40 ∧
      framePeak ((prepareWithTrace entries).2.take steps) ≤
        PRGPhysicalArrayInterface.preparationBound length+2*length+40 := by
  simpa only [Nat.add_assoc] using BinaryPRGHeapTraceUsage.all_prefix _ _
    (prepareWithTrace_raw_bound length n entries hEntries hn hWidth) borrowed steps

theorem physical_store_caps (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22) :
    (prepareWithTrace entries).1.heap.tape.length ≤
        PRGPhysicalArrayInterface.heapCap length ∧
      (prepareWithTrace entries).1.slots.length ≤
        PRGPhysicalArrayInterface.slotsCap length := by
  have hPayload := BinaryWordObjectArray.payloadBits_bound (words entries)
    (9*length+22) hWidth
  have hCount : (words entries).length = n := by rw [words_length,hEntries]
  rw [hCount] at hPayload
  have hCap : BinaryWordObjectArray.payloadBits (words entries) ≤
      PRGPhysicalArrayInterface.heapCap length := by
    unfold PRGPhysicalArrayInterface.heapCap
    nlinarith
  have hHeap : (prepareWithTrace entries).1.heap.tape.length =
      BinaryWordObjectArray.payloadBits (words entries) := by
    simp only [prepareWithTrace,BinaryWordObjectArrayLifetime.prepareWithTrace_state]
    rw [projected_trace_words,BinaryWordObjectArray.prepare_heap_length]
  have hSlots := (prepareWithTrace entries).1.slots_bound
  have hProjectedLength :
      (BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries).1.length = n := by
    rw [projected_trace_words,hCount]
  have hSlotCount : (prepareWithTrace entries).1.slots.length ≤
      n*(2*binaryWordWidth
        (prepareWithTrace entries).1.heap.tape.length+1) := by
    simpa only [prepareWithTrace,hProjectedLength] using hSlots
  have hWordWidth := (PRGPhysicalArrayInterface.wordWidth_le
    (prepareWithTrace entries).1.heap.tape.length).trans
    (Nat.add_le_add_right (hHeap.trans_le hCap) 1)
  refine ⟨hHeap.trans_le hCap,?_⟩
  unfold PRGPhysicalArrayInterface.slotsCap
  nlinarith

theorem physical_read_raw_bounds (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22)
    (index : List Bool) (hIndex : index.length ≤ length+1) :
    (BinaryWordObjectArray.getWithWork (prepareWithTrace entries).1 index).2 ≤
        PRGPhysicalArrayInterface.readWorkBound length ∧
      usage (BinaryWordObjectArrayAccess.getWithTrace (prepareWithTrace entries).1 index).2 ≤
        PRGPhysicalArrayInterface.readEnvelope length := by
  have hCaps := physical_store_caps length n entries hEntries hn hWidth
  have hWordWidth := (PRGPhysicalArrayInterface.wordWidth_le
    (prepareWithTrace entries).1.heap.tape.length).trans
    (Nat.add_le_add_right hCaps.1 1)
  constructor
  · apply (BinaryWordObjectArray.getWithWork_bound _ _).trans
    unfold BinaryWordObjectArray.readBound PRGPhysicalArrayInterface.readWorkBound
      BinaryReferenceVector.readBound BinaryPRGWordStoreHeapMachine.readBound
      BinaryPRGWordStoreHeapMachine.skipBound
    gcongr <;> omega
  · apply (BinaryWordObjectArrayAccess.get_usage _ _).trans
    unfold BinaryWordObjectArrayAccess.envelope BinaryWordObjectArrayAccess.heapReadEnvelope
      PRGPhysicalArrayInterface.readEnvelope BinaryReferenceVector.readBound
      BinaryPRGWordStoreHeapMachine.readBound BinaryPRGWordStoreHeapMachine.skipBound
    gcongr <;> omega

def runWithWork (entries : List (SignedWord × Trace)) (index : List Bool) :
    Option SignedWord × ℕ :=
  let prepared := prepareWithWork entries
  let result := BinaryWordObjectArray.getWithWork prepared.1 index
  (result.1,prepared.2+result.2+8)

def runWithTrace (entries : List (SignedWord × Trace)) (index : List Bool) :
    Option SignedWord × Trace :=
  let prepared := prepareWithTrace entries
  let result := BinaryWordObjectArrayAccess.getWithTrace prepared.1 index
  (result.1,wrap 64 2 [prepared.2,result.2])

theorem runWithWork_readback (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (runWithWork entries index).1 =
      some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) :=
  prepareWithWork_readback n entries hEntries index j hIndex

theorem runWithTrace_readback (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (runWithTrace entries index).1 =
      some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) :=
  prepareWithTrace_readback n entries hEntries index j hIndex

theorem runWithWork_raw_bound (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22)
    (index : List Bool) (hIndex : index.length ≤ length+1) :
    (runWithWork entries index).2 ≤
      PRGPhysicalArrayInterface.preparationBound length+length+8+
        PRGPhysicalArrayInterface.readWorkBound length+8 := by
  have hPrep := prepareWithWork_raw_bound length n entries hEntries hn hWidth
  have hRead := (physical_read_raw_bounds length n entries hEntries hn hWidth index hIndex).1
  have hStores : (prepareWithWork entries).1.heap = (prepareWithTrace entries).1.heap ∧
      (prepareWithWork entries).1.slots = (prepareWithTrace entries).1.slots := by
    simp only [prepareWithWork,prepareWithTrace,
      BinaryWordObjectArrayLifetime.prepareWithWork_state,
      BinaryWordObjectArrayLifetime.prepareWithTrace_state]
    rw [projected_work_words,projected_trace_words]
    exact ⟨rfl,rfl⟩
  have hStoreRead : (BinaryWordObjectArray.getWithWork (prepareWithWork entries).1 index).2 =
      (BinaryWordObjectArray.getWithWork (prepareWithTrace entries).1 index).2 := by
    unfold BinaryWordObjectArray.getWithWork
    rw [hStores.1,hStores.2]
  change _+_+8 ≤ _
  rw [hStoreRead]
  omega

theorem runWithTrace_raw_bound (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22)
    (index : List Bool) (hIndex : index.length ≤ length+1) :
    usage (runWithTrace entries index).2 ≤
      PRGPhysicalArrayInterface.preparationBound length+2*length+40+
        PRGPhysicalArrayInterface.readEnvelope length+128 := by
  have hPrep := prepareWithTrace_raw_bound length n entries hEntries hn hWidth
  have hRead := (physical_read_raw_bounds length n entries hEntries hn hWidth index hIndex).2
  have hWrap := wrap_usage 64 2 [(prepareWithTrace entries).2,
    (BinaryWordObjectArrayAccess.getWithTrace (prepareWithTrace entries).1 index).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change usage (runWithTrace entries index).2 ≤ _ at hWrap
  omega

theorem runWithTrace_raw_prefix (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22)
    (index : List Bool) (hIndex : index.length ≤ length+1)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace entries index).2 steps ≤
        borrowed+PRGPhysicalArrayInterface.preparationBound length+2*length+40+
          PRGPhysicalArrayInterface.readEnvelope length+128 ∧
      framePeak ((runWithTrace entries index).2.take steps) ≤
        PRGPhysicalArrayInterface.preparationBound length+2*length+40+
          PRGPhysicalArrayInterface.readEnvelope length+128 := by
  simpa only [Nat.add_assoc] using BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_raw_bound length n entries hEntries hn hWidth index hIndex) borrowed steps

theorem word_for_index (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (j : Fin n) :
    ∃ index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace (words entries)).1,
      BinaryBigEndian.littleValue index = j.val := by
  have hValues := BooleanArrayIndexEnumeration.enumerate_values (words entries)
  rw [words_length,hEntries] at hValues
  have hMem : j.val ∈
      ((BooleanArrayIndexEnumeration.enumerateWithTrace (words entries)).1.map
        BinaryCarryCounter.value) := by
    rw [hValues]
    exact List.mem_range.mpr j.isLt
  obtain ⟨index,hIndex,hValue⟩ := List.mem_map.mp hMem
  exact ⟨index,hIndex,hValue⟩

theorem physical_lookup_raw (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22)
    (j : Fin n) :
    ∃ index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace (words entries)).1,
      (runWithWork entries index).1 =
        some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) ∧
      (runWithTrace entries index).1 =
        some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) ∧
      (runWithWork entries index).2 ≤
        PRGPhysicalArrayInterface.preparationBound length+length+8+
          PRGPhysicalArrayInterface.readWorkBound length+8 ∧
      usage (runWithTrace entries index).2 ≤
        PRGPhysicalArrayInterface.preparationBound length+2*length+40+
          PRGPhysicalArrayInterface.readEnvelope length+128 := by
  obtain ⟨index,hIndex,hValue⟩ := word_for_index n entries hEntries j
  have hIndexWidth := BooleanArrayIndexEnumeration.enumerate_width (words entries)
    index hIndex
  rw [words_length,hEntries] at hIndexWidth
  have hIndexBound : index.length ≤ length+1 :=
    hIndexWidth.trans ((PRGPhysicalArrayInterface.wordWidth_le n).trans
      (Nat.add_le_add_right hn 1))
  exact ⟨index,hIndex,runWithWork_readback n entries hEntries index j hValue,
    runWithTrace_readback n entries hEntries index j hValue,
    runWithWork_raw_bound length n entries hEntries hn hWidth index hIndexBound,
    runWithTrace_raw_bound length n entries hEntries hn hWidth index hIndexBound⟩

theorem selected_pair_readback {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    (BinaryWordObjectArrayAccess.getWithTrace
      (preparePairWithTrace lengthEntries poorEntries).1.1 index).1 =
        some ((BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows hRows).1.lengths.read j) ∧
    (BinaryWordObjectArrayAccess.getWithTrace
      (preparePairWithTrace lengthEntries poorEntries).2.1 index).1 =
        some ((BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows hRows).1.poorResources.read j) := by
  dsimp only
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  have hLength : lengthEntries.length = n := by
    dsimp only [lengthEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hRows,List.length_ofFn]
  have hPoor : poorEntries.length = n := by
    dsimp only [poorEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hLength]
  constructor
  · simpa only [preparePairWithTrace,BinaryPRGNumericalPreparationLifetime.prepareWithRows] using
      prepareWithTrace_readback n lengthEntries hLength index j hIndex
  · simpa only [preparePairWithTrace,BinaryPRGNumericalPreparationLifetime.prepareWithRows] using
      prepareWithTrace_readback n poorEntries hPoor index j hIndex

theorem parsed_pair_raw_bounds (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    usage (preparePairWithTrace lengthEntries poorEntries).1.2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40 ∧
      usage (preparePairWithTrace lengthEntries poorEntries).2.2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40 ∧
      (prepareWithWork lengthEntries).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+bits.length+8 ∧
      (prepareWithWork poorEntries).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+bits.length+8 := by
  have hEnvelope := BinaryPRGNumericalPhysicalEntries.parsed_pair_raw_envelopes bits parsed h
  dsimp only at hEnvelope ⊢
  let input := parsed.1.2.game.input
  let rows := parsed.1.2.rows
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  have hSizes := BinaryPRGCheckedGameLifetime.parsed_sizes bits parsed h
  have hLength : lengthEntries.length = parsed.1.1 := by
    dsimp only [lengthEntries]
    rw [BinaryLifetimeArray.mapDirect_length,parsed.1.2.rows_length]
  have hPoor : poorEntries.length = parsed.1.1 := by
    dsimp only [poorEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hLength]
  have hTraceLength := prepareWithTrace_usage lengthEntries
  have hTracePoor := prepareWithTrace_usage poorEntries
  have hWorkLength := prepareWithWork_bound lengthEntries
  have hWorkPoor := prepareWithWork_bound poorEntries
  rw [hLength] at hTraceLength hWorkLength
  rw [hPoor] at hTracePoor hWorkPoor
  have hEnvLength : BinaryWordObjectArrayLifetime.envelope (words lengthEntries) ≤
      PRGPhysicalArrayInterface.preparationBound bits.length := hEnvelope.1
  have hEnvPoor : BinaryWordObjectArrayLifetime.envelope (words poorEntries) ≤
      PRGPhysicalArrayInterface.preparationBound bits.length := hEnvelope.2
  simpa only [preparePairWithTrace] using
    (show usage (prepareWithTrace lengthEntries).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40 ∧
      usage (prepareWithTrace poorEntries).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40 ∧
      (prepareWithWork lengthEntries).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+bits.length+8 ∧
      (prepareWithWork poorEntries).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+bits.length+8 from
      ⟨by omega,by omega,by omega,by omega⟩)

theorem parsed_pair_raw_prefix (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed)
    (borrowed steps : ℕ) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    retainedHeap borrowed (preparePairWithTrace lengthEntries poorEntries).1.2 steps ≤
        borrowed+PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40 ∧
      framePeak ((preparePairWithTrace lengthEntries poorEntries).1.2.take steps) ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40 ∧
      retainedHeap borrowed (preparePairWithTrace lengthEntries poorEntries).2.2 steps ≤
        borrowed+PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40 ∧
      framePeak ((preparePairWithTrace lengthEntries poorEntries).2.2.take steps) ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40 := by
  have hBounds := parsed_pair_raw_bounds bits parsed h
  dsimp only at hBounds ⊢
  have hFirst := BinaryPRGHeapTraceUsage.all_prefix _ _ hBounds.1 borrowed steps
  have hSecond := BinaryPRGHeapTraceUsage.all_prefix _ _ hBounds.2.1 borrowed steps
  exact ⟨by simpa only [Nat.add_assoc] using hFirst.1,hFirst.2,
    by simpa only [Nat.add_assoc] using hSecond.1,hSecond.2⟩

theorem parsed_pair_raw_lookup (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed)
    (j : Fin parsed.1.1) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    (∃ index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace (words lengthEntries)).1,
      (runWithTrace lengthEntries index).1 =
        some ((BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows
          parsed.1.2.rows_readback).1.lengths.read j) ∧
      (runWithWork lengthEntries index).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+bits.length+8+
          PRGPhysicalArrayInterface.readWorkBound bits.length+8 ∧
      usage (runWithTrace lengthEntries index).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40+
          PRGPhysicalArrayInterface.readEnvelope bits.length+128) ∧
    (∃ index ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace (words poorEntries)).1,
      (runWithTrace poorEntries index).1 =
        some ((BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows
          parsed.1.2.rows_readback).1.poorResources.read j) ∧
      (runWithWork poorEntries index).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+bits.length+8+
          PRGPhysicalArrayInterface.readWorkBound bits.length+8 ∧
      usage (runWithTrace poorEntries index).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40+
          PRGPhysicalArrayInterface.readEnvelope bits.length+128) := by
  dsimp only
  let input := parsed.1.2.game.input
  let rows := parsed.1.2.rows
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  have hSizes := BinaryPRGCheckedGameLifetime.parsed_sizes bits parsed h
  have hLength : lengthEntries.length = parsed.1.1 := by
    dsimp only [lengthEntries]
    rw [BinaryLifetimeArray.mapDirect_length,parsed.1.2.rows_length]
  have hPoor : poorEntries.length = parsed.1.1 := by
    dsimp only [poorEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hLength]
  have hWidths := BinaryPRGNumericalPhysicalEntries.selected_widths input
    parsed.1.2.game.canonical rows parsed.1.2.rows_readback
  dsimp only [input,rows,ratio,lengthEntries,poorEntries] at hWidths
  have hFirstWidth : ∀ word ∈ words lengthEntries,
      width word ≤ 9*bits.length+22 := by
    intro word hw
    have := hWidths.1 word hw
    omega
  have hSecondWidth : ∀ word ∈ words poorEntries,
      width word ≤ 9*bits.length+22 := by
    intro word hw
    have := hWidths.2 word hw
    omega
  obtain ⟨first,hFirstMem,_hFirstWorkValue,hFirstValue,hFirstWork,hFirstTrace⟩ :=
    physical_lookup_raw bits.length parsed.1.1 lengthEntries hLength hSizes.1 hFirstWidth j
  obtain ⟨second,hSecondMem,_hSecondWorkValue,hSecondValue,hSecondWork,hSecondTrace⟩ :=
    physical_lookup_raw bits.length parsed.1.1 poorEntries hPoor hSizes.1 hSecondWidth j
  refine ⟨⟨first,hFirstMem,?_,hFirstWork,hFirstTrace⟩,
    ⟨second,hSecondMem,?_,hSecondWork,hSecondTrace⟩⟩
  · simpa only [BinaryPRGNumericalPreparationLifetime.prepareWithRows] using hFirstValue
  · simpa only [BinaryPRGNumericalPreparationLifetime.prepareWithRows] using hSecondValue

end Blotto.BinaryPRGNumericalPhysicalMapLifetime
