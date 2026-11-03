import Blotto.BinaryPRGNumericalPackControl
import Blotto.BinaryWordObjectArrayAccess
import Blotto.PRGPhysicalArrayInterface

/-! The selected numerical maps retain value/trace entries before packing
their two native output tables. This alternative physical constructor takes
those entries directly: it projects their values with the structural map and
allocates Boolean leaf objects and pointer slots. Its execution never reads
back a native array or calls `Array.toList`. The native tables appear only in
the readback proof. Selection by the complete sampler is separate. -/
namespace Blotto.BinaryPRGNumericalPhysicalEntries
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGRecognition
open BinaryPRGPreparation BinaryWordObjectArray BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def words (entries : List (SignedWord × Trace)) : List SignedWord :=
  BinaryLifetimeArray.mapDirect Prod.fst entries

def prepareEntries (entries : List (SignedWord × Trace)) :
    Store (words entries).length × Trace :=
  BinaryWordObjectArrayLifetime.prepareWithTrace (words entries)

def preparePair (lengthEntries poorEntries : List (SignedWord × Trace)) :=
  (prepareEntries lengthEntries, prepareEntries poorEntries)

theorem words_length (entries : List (SignedWord × Trace)) :
    (words entries).length = entries.length :=
  BinaryLifetimeArray.mapDirect_length Prod.fst entries

theorem words_native_readback (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) :
    words entries = (BinaryLifetimeArray.fromEntries n entries hEntries).1.data.toList := by
  simp only [words,BinaryLifetimeArray.fromEntries,BinaryLifetimeArray.packEntries_state,
    List.toList_toArray]

theorem physical_readback (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace (prepareEntries entries).1 index).1 =
      some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) := by
  rw [BinaryWordObjectArrayAccess.get_realizes _ _
    (by rw [prepareEntries,BinaryWordObjectArrayLifetime.prepareWithTrace_state]
        exact BinaryWordObjectArray.prepare_realizes (words entries))]
  rw [hIndex]
  have hLen : (words entries).length = n := by rw [words_length,hEntries]
  rw [List.getElem?_eq_getElem (by rw [hLen]; exact j.isLt)]
  congr 1
  rw [BinaryLifetimeArray.fromEntries_read]
  simp [words,BinaryLifetimeArray.mapDirect_eq_map]

theorem physical_heap_length (entries : List (SignedWord × Trace)) :
    (prepareEntries entries).1.heap.tape.length = payloadBits (words entries) := by
  rw [prepareEntries,BinaryWordObjectArrayLifetime.prepareWithTrace_state,
    BinaryWordObjectArray.prepare_heap_length]

theorem physical_usage (entries : List (SignedWord × Trace)) :
    usage (prepareEntries entries).2 ≤ BinaryWordObjectArrayLifetime.envelope (words entries) :=
  BinaryWordObjectArrayLifetime.prepare_usage (words entries)

theorem physical_prefix (entries : List (SignedWord × Trace)) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareEntries entries).2 steps ≤
        borrowed + BinaryWordObjectArrayLifetime.envelope (words entries) ∧
      framePeak ((prepareEntries entries).2.take steps) ≤
        BinaryWordObjectArrayLifetime.envelope (words entries) :=
  BinaryWordObjectArrayLifetime.all_prefix (words entries) borrowed steps

theorem physical_raw_envelope (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22) :
    BinaryWordObjectArrayLifetime.envelope (words entries) ≤
      PRGPhysicalArrayInterface.preparationBound length := by
  have hPayload := payloadBits_bound (words entries) (9*length+22) hWidth
  rw [words_length,hEntries] at hPayload
  have hCap : payloadBits (words entries) ≤ PRGPhysicalArrayInterface.heapCap length := by
    unfold PRGPhysicalArrayInterface.heapCap
    nlinarith
  have hBinary := (PRGPhysicalArrayInterface.wordWidth_le (payloadBits (words entries))).trans
    (Nat.add_le_add_right hCap 1)
  have hCount : (words entries).length ≤ length := by rw [words_length,hEntries]; exact hn
  unfold BinaryWordObjectArrayLifetime.envelope BinaryPRGWordStoreHeapMachine.allocationBound
    PRGPhysicalArrayInterface.preparationBound
  gcongr

theorem physical_raw_usage (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22) :
    usage (prepareEntries entries).2 ≤ PRGPhysicalArrayInterface.preparationBound length :=
  (physical_usage entries).trans (physical_raw_envelope length n entries hEntries hn hWidth)

theorem physical_raw_prefix (length n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (hn : n ≤ length)
    (hWidth : ∀ word ∈ words entries, width word ≤ 9*length+22)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareEntries entries).2 steps ≤
        borrowed + PRGPhysicalArrayInterface.preparationBound length ∧
      framePeak ((prepareEntries entries).2.take steps) ≤
        PRGPhysicalArrayInterface.preparationBound length := by
  have h := physical_prefix entries borrowed steps
  have hBound := physical_raw_envelope length n entries hEntries hn hWidth
  exact ⟨h.1.trans (Nat.add_le_add_left hBound borrowed),h.2.trans hBound⟩

theorem selected_readback {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    (BinaryWordObjectArrayAccess.getWithTrace
      (preparePair lengthEntries poorEntries).1.1 index).1 =
        some ((BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows hRows).1.lengths.read j) ∧
    (BinaryWordObjectArrayAccess.getWithTrace
      (preparePair lengthEntries poorEntries).2.1 index).1 =
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
  · simpa only [preparePair,BinaryPRGNumericalPreparationLifetime.prepareWithRows] using
      physical_readback n lengthEntries hLength index j hIndex
  · simpa only [preparePair,BinaryPRGNumericalPreparationLifetime.prepareWithRows] using
      physical_readback n poorEntries hPoor index j hIndex

theorem selected_widths {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    (∀ word ∈ words lengthEntries,
      width word ≤ 9*BinaryPRGPreparationWork.storedInputWidth input+4) ∧
    (∀ word ∈ words poorEntries,
      width word ≤ 9*BinaryPRGPreparationWork.storedInputWidth input+4) := by
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
  have hPrep := BinaryPRGNumericalPreparationLifetime.prepareWithRows_state input hC rows hRows
  have hTableLength : (BinaryLifetimeArray.fromEntries n lengthEntries hLength).1 =
      (prepare input).lengths := by
    have h := congrArg Prepared.lengths hPrep
    simpa only [BinaryPRGNumericalPreparationLifetime.prepareWithRows] using h
  have hTablePoor : (BinaryLifetimeArray.fromEntries n poorEntries hPoor).1 =
      (prepare input).poorResources := by
    have h := congrArg Prepared.poorResources hPrep
    simpa only [BinaryPRGNumericalPreparationLifetime.prepareWithRows] using h
  constructor
  · rw [words_native_readback n lengthEntries hLength]
    apply PRGPhysicalArrayInterface.table_list_width
    intro j
    rw [hTableLength]
    have h := BinaryPRGPreparationWork.lengths_width input j
    omega
  · rw [words_native_readback n poorEntries hPoor]
    apply PRGPhysicalArrayInterface.table_list_width
    intro j
    rw [hTablePoor]
    exact BinaryPRGPreparationWork.poorResources_width input j

theorem parsed_pair_raw_envelopes (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    BinaryWordObjectArrayLifetime.envelope (words lengthEntries) ≤
        PRGPhysicalArrayInterface.preparationBound bits.length ∧
      BinaryWordObjectArrayLifetime.envelope (words poorEntries) ≤
        PRGPhysicalArrayInterface.preparationBound bits.length := by
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
  have hWidths := selected_widths input parsed.1.2.game.canonical rows
    parsed.1.2.rows_readback
  dsimp only [input,rows,ratio,lengthEntries,poorEntries] at hWidths
  have hFirst : ∀ word ∈ words lengthEntries, width word ≤ 9*bits.length+22 := by
    intro word hw
    have := hWidths.1 word hw
    omega
  have hSecond : ∀ word ∈ words poorEntries, width word ≤ 9*bits.length+22 := by
    intro word hw
    have := hWidths.2 word hw
    omega
  exact ⟨physical_raw_envelope bits.length parsed.1.1 lengthEntries hLength hSizes.1 hFirst,
    physical_raw_envelope bits.length parsed.1.1 poorEntries hPoor hSizes.1 hSecond⟩

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
    usage (preparePair lengthEntries poorEntries).1.2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length ∧
      usage (preparePair lengthEntries poorEntries).2.2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length := by
  have hEnvelope := parsed_pair_raw_envelopes bits parsed h
  dsimp only at hEnvelope ⊢
  exact ⟨(physical_usage _).trans hEnvelope.1,
    (physical_usage _).trans hEnvelope.2⟩

theorem parsed_pair_raw_work (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    (BinaryWordObjectArrayLifetime.prepareWithWork (words lengthEntries)).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length ∧
      (BinaryWordObjectArrayLifetime.prepareWithWork (words poorEntries)).2 ≤
        PRGPhysicalArrayInterface.preparationBound bits.length := by
  have hEnvelope := parsed_pair_raw_envelopes bits parsed h
  dsimp only at hEnvelope ⊢
  exact ⟨(BinaryWordObjectArrayLifetime.prepareWithWork_bound _).trans
      ((PRGPhysicalArrayInterface.workEnvelope_le_source _).trans hEnvelope.1),
    (BinaryWordObjectArrayLifetime.prepareWithWork_bound _).trans
      ((PRGPhysicalArrayInterface.workEnvelope_le_source _).trans hEnvelope.2)⟩

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
    retainedHeap borrowed (preparePair lengthEntries poorEntries).1.2 steps ≤
        borrowed + PRGPhysicalArrayInterface.preparationBound bits.length ∧
      framePeak ((preparePair lengthEntries poorEntries).1.2.take steps) ≤
        PRGPhysicalArrayInterface.preparationBound bits.length ∧
      retainedHeap borrowed (preparePair lengthEntries poorEntries).2.2 steps ≤
        borrowed + PRGPhysicalArrayInterface.preparationBound bits.length ∧
      framePeak ((preparePair lengthEntries poorEntries).2.2.take steps) ≤
        PRGPhysicalArrayInterface.preparationBound bits.length := by
  have hUsage := parsed_pair_raw_bounds bits parsed h
  dsimp only at hUsage ⊢
  have hFirst := BinaryPRGHeapTraceUsage.all_prefix _ _ hUsage.1 borrowed steps
  have hSecond := BinaryPRGHeapTraceUsage.all_prefix _ _ hUsage.2 borrowed steps
  exact ⟨hFirst.1,hFirst.2,hSecond.1,hSecond.2⟩

end Blotto.BinaryPRGNumericalPhysicalEntries
