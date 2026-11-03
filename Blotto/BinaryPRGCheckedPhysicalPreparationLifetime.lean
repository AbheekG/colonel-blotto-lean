import Blotto.BinaryPRGCheckedPreparationLifetime
import Blotto.BinaryPRGNumericalPhysicalMapLifetime

/-! On acceptance, one numerical preparation retains its two arithmetic
entry lists long enough to build both compatibility native tables and the
measured physical word-object stores. The promise check still runs first;
rejection does no numerical or physical preparation. This is the next
interface toward downstream physical-table selection, not yet a change to
the complete sampler's request type. -/
namespace Blotto.BinaryPRGCheckedPhysicalPreparationLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGRecognition
open BinaryPRGPreparation BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def castStore {m n : ℕ} (h : m = n) (store : BinaryWordObjectArray.Store m) :
    BinaryWordObjectArray.Store n := h ▸ store

theorem get_castStore {m n : ℕ} (h : m = n) (store : BinaryWordObjectArray.Store m)
    (index : List Bool) :
    BinaryWordObjectArrayAccess.getWithTrace (castStore h store) index =
      BinaryWordObjectArrayAccess.getWithTrace store index := by
  cases h
  rfl

def fixedPhysical (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) : BinaryWordObjectArray.Store n × Trace :=
  let physical := BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace entries
  have hSize : (BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries).1.length = n := by
    rw [BinaryPRGNumericalPhysicalMapLifetime.projected_trace_words,
      BinaryPRGNumericalPhysicalEntries.words_length,hEntries]
  (castStore hSize physical.1,physical.2)

theorem fixedPhysical_readback (n : ℕ) (entries : List (SignedWord × Trace))
    (hEntries : entries.length = n) (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace (fixedPhysical n entries hEntries).1 index).1 =
      some ((BinaryLifetimeArray.fromEntries n entries hEntries).1.read j) := by
  simp only [fixedPhysical,get_castStore]
  exact BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace_readback
    n entries hEntries index j hIndex

structure PreparedPhysical (n : ℕ) where
  numerical : Prepared n
  lengthStore : BinaryWordObjectArray.Store n
  poorStore : BinaryWordObjectArray.Store n
  readback : ∀ (index : List Bool) (j : Fin n),
    BinaryBigEndian.littleValue index = j.val →
      (BinaryWordObjectArrayAccess.getWithTrace lengthStore index).1 =
          some (numerical.lengths.read j) ∧
        (BinaryWordObjectArrayAccess.getWithTrace poorStore index).1 =
          some (numerical.poorResources.read j)

def prepareWithRowsPhysical {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) : PreparedPhysical n × Trace :=
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let hLength : lengthEntries.length = n := by
    simp [lengthEntries,BinaryLifetimeArray.mapDirect_length,hRows]
  let lengths := BinaryLifetimeArray.fromEntries n lengthEntries hLength
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  let hPoor : poorEntries.length = n := by
    simp [poorEntries,lengthEntries,BinaryLifetimeArray.mapDirect_length,hRows]
  let poor := BinaryLifetimeArray.fromEntries n poorEntries hPoor
  let physicalLength := fixedPhysical n lengthEntries hLength
  let physicalPoor := fixedPhysical n poorEntries hPoor
  let numericalTrace := wrapList
    (6*n+BinaryPRGNumericalPreparationLifetime.flattenListReserve n
      (BinaryPRGPreparationWork.storedInputWidth input))
    (64+BinaryPRGNumericalPreparationLifetime.flattenArrayReserve n
      (BinaryPRGPreparationWork.storedInputWidth input))
    (n+4) [ratio.2,lengths.2,poor.2]
  (⟨⟨input,ratio.1,lengths.1,poor.1⟩,physicalLength.1,physicalPoor.1,
      (by
        intro index j hIndex
        exact ⟨fixedPhysical_readback n lengthEntries hLength index j hIndex,
          fixedPhysical_readback n poorEntries hPoor index j hIndex⟩)⟩,
    wrap 128 2 [numericalTrace,physicalLength.2,physicalPoor.2])

theorem prepareWithRowsPhysical_numerical {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (prepareWithRowsPhysical input rows hRows).1.numerical =
      (BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows hRows).1 := by
  rfl

theorem prepareWithRowsPhysical_readback {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace
      (prepareWithRowsPhysical input rows hRows).1.lengthStore index).1 =
        some ((prepareWithRowsPhysical input rows hRows).1.numerical.lengths.read j) ∧
    (BinaryWordObjectArrayAccess.getWithTrace
      (prepareWithRowsPhysical input rows hRows).1.poorStore index).1 =
        some ((prepareWithRowsPhysical input rows hRows).1.numerical.poorResources.read j) := by
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
  · simpa only [prepareWithRowsPhysical] using
      fixedPhysical_readback n lengthEntries hLength index j hIndex
  · simpa only [prepareWithRowsPhysical] using
      fixedPhysical_readback n poorEntries hPoor index j hIndex

theorem prepareWithRowsPhysical_usage_parts {n : ℕ} (input : Input n)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    usage (prepareWithRowsPhysical input rows hRows).2 ≤
      usage (BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows hRows).2+
      usage (BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace lengthEntries).2+
      usage (BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace poorEntries).2+136 := by
  dsimp only
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  have hWrap := wrap_usage 128 2
    [(BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows hRows).2,
      (BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace lengthEntries).2,
      (BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace poorEntries).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  change usage (prepareWithRowsPhysical input rows hRows).2 ≤ _ at hWrap
  dsimp only [ratio,lengthEntries,poorEntries] at hWrap ⊢
  omega

def prepareCheckedPhysicalWithRows {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    Option {prepared : PreparedPhysical n // prepared.numerical.Valid} × Trace :=
  let checked := BinaryPRGPromiseLifetime.checkRowsWithTrace input rows
  if h : checked.1 = true then
    let prepared := prepareWithRowsPhysical input rows hRows
    have hCheck : input.Checks := (checkBool_iff input hC).mp
      ((BinaryPRGPromiseLifetime.checkRowsWithTrace_state input hC rows hRows).symm.trans h)
    have hValid : prepared.1.numerical.Valid := by
      rw [prepareWithRowsPhysical_numerical,
        BinaryPRGNumericalPreparationLifetime.prepareWithRows_state input hC rows hRows]
      exact prepare_valid input hC hCheck
    (some ⟨prepared.1,hValid⟩,wrap 32 2 [checked.2,prepared.2])
  else (none,wrap 16 2 [checked.2])

def forgetPhysical {n : ℕ} (prepared : {p : PreparedPhysical n // p.numerical.Valid}) :
    {p : Prepared n // p.Valid} := ⟨prepared.1.numerical,prepared.2⟩

theorem prepareCheckedPhysical_refines {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (prepareCheckedPhysicalWithRows input hC rows hRows).1.map forgetPhysical =
      (BinaryPRGCheckedPreparationLifetime.prepareCheckedWithRows input hC rows hRows).1 := by
  unfold prepareCheckedPhysicalWithRows BinaryPRGCheckedPreparationLifetime.prepareCheckedWithRows
  dsimp only
  split
  · simp only [Option.map_some]
    apply congrArg some
    apply Subtype.ext
    exact prepareWithRowsPhysical_numerical input rows hRows
  · rfl

theorem prepareCheckedPhysical_isSome {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (prepareCheckedPhysicalWithRows input hC rows hRows).1.isSome = true ↔ input.Checks := by
  have hRefines := prepareCheckedPhysical_refines input hC rows hRows
  have hSome := congrArg Option.isSome hRefines
  rw [Option.isSome_map] at hSome
  rw [hSome,BinaryPRGCheckedPreparationLifetime.prepareCheckedWithRows_state]
  exact prepareChecked_isSome input hC

theorem checked_result_readback {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (result : {p : PreparedPhysical n // p.numerical.Valid})
    (hResult : (prepareCheckedPhysicalWithRows input hC rows hRows).1 = some result)
    (index : List Bool) (j : Fin n)
    (hIndex : BinaryBigEndian.littleValue index = j.val) :
    (BinaryWordObjectArrayAccess.getWithTrace result.1.lengthStore index).1 =
        some (result.1.numerical.lengths.read j) ∧
    (BinaryWordObjectArrayAccess.getWithTrace result.1.poorStore index).1 =
        some (result.1.numerical.poorResources.read j) := by
  unfold prepareCheckedPhysicalWithRows at hResult
  dsimp only at hResult
  split at hResult
  · obtain ⟨⟩ := Option.some.inj hResult
    exact prepareWithRowsPhysical_readback input rows hRows index j hIndex
  · cases hResult

theorem rejected_trace {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (hReject : (BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).1 ≠ true) :
    (prepareCheckedPhysicalWithRows input hC rows hRows).2 =
      wrap 16 2 [(BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).2] := by
  simp only [prepareCheckedPhysicalWithRows,dite_eq_right hReject]

theorem accepted_trace {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (hAccept : (BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).1 = true) :
    (prepareCheckedPhysicalWithRows input hC rows hRows).2 =
      wrap 32 2 [(BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).2,
        (prepareWithRowsPhysical input rows hRows).2] := by
  simp only [prepareCheckedPhysicalWithRows,dite_eq_left hAccept]

private theorem accepted_wrap_usage (a b : Trace) :
    usage (wrap 32 2 [a,b]) ≤ usage a + usage b + 64 := by
  have hWrap := wrap_usage 32 2 [a,b]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  omega

private theorem rejected_wrap_usage (a : Trace) :
    usage (wrap 16 2 [a]) ≤ usage a + 64 := by
  have hWrap := wrap_usage 16 2 [a]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  omega

set_option maxHeartbeats 100000 in
theorem prepareCheckedPhysical_usage_parts {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    usage (prepareCheckedPhysicalWithRows input hC rows hRows).2 ≤
      usage (BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).2+
        usage (prepareWithRowsPhysical input rows hRows).2+64 := by
  by_cases hAccept : (BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).1 = true
  · calc
      usage (prepareCheckedPhysicalWithRows input hC rows hRows).2 =
          usage (wrap 32 2 [(BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).2,
            (prepareWithRowsPhysical input rows hRows).2]) :=
        congrArg usage (accepted_trace input hC rows hRows hAccept)
      _ ≤ _ := accepted_wrap_usage _ _
  · calc
      usage (prepareCheckedPhysicalWithRows input hC rows hRows).2 =
          usage (wrap 16 2 [(BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).2]) :=
        congrArg usage (rejected_trace input hC rows hRows hAccept)
      _ ≤ usage (BinaryPRGPromiseLifetime.checkRowsWithTrace input rows).2 + 64 :=
        rejected_wrap_usage _
      _ ≤ _ := by omega

set_option maxHeartbeats 100000 in
theorem parsed_numerical_physical_usage (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    usage (prepareWithRowsPhysical parsed.1.2.game.input parsed.1.2.rows
      parsed.1.2.rows_readback).2 ≤
      BinaryPRGNumericalPreparationLifetime.envelope bits.length (bits.length+2)+
        2*(PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40)+136 := by
  let input := parsed.1.2.game.input
  let rows := parsed.1.2.rows
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  have hSizes := BinaryPRGCheckedGameLifetime.parsed_sizes bits parsed h
  have hParts := prepareWithRowsPhysical_usage_parts input rows parsed.1.2.rows_readback
  have hNumerical := BinaryPRGNumericalPreparationLifetime.prepareWithRows_usage
    input parsed.1.2.game.canonical rows parsed.1.2.rows_readback
  have hNumericalRaw := hNumerical.trans
    (BinaryPRGNumericalPreparationLifetime.envelope_mono hSizes.1 hSizes.2)
  have hPhysical := BinaryPRGNumericalPhysicalMapLifetime.parsed_pair_raw_bounds bits parsed h
  simp only [BinaryPRGNumericalPhysicalMapLifetime.preparePairWithTrace] at hPhysical
  dsimp only [input,rows,ratio,lengthEntries,poorEntries] at hParts hPhysical hNumericalRaw ⊢
  omega

set_option maxHeartbeats 100000 in
theorem parsed_checked_physical_usage (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    usage (prepareCheckedPhysicalWithRows parsed.1.2.game.input
      parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).2 ≤
      BinaryPRGPromiseLifetime.envelope bits.length (bits.length+2)+
      BinaryPRGNumericalPreparationLifetime.envelope bits.length (bits.length+2)+
      2*(PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40)+256 := by
  let input := parsed.1.2.game.input
  let rows := parsed.1.2.rows
  have hSizes := BinaryPRGCheckedGameLifetime.parsed_sizes bits parsed h
  have hCheck := BinaryPRGPromiseLifetime.checkRowsWithTrace_usage input
    parsed.1.2.game.canonical rows parsed.1.2.rows_readback
  have hCheckRaw := hCheck.trans
    (BinaryPRGPromiseLifetime.envelope_mono hSizes.1 hSizes.2)
  have hNumerical := parsed_numerical_physical_usage bits parsed h
  have hParts := prepareCheckedPhysical_usage_parts input parsed.1.2.game.canonical
    rows parsed.1.2.rows_readback
  dsimp only [input,rows] at hParts hCheckRaw hNumerical ⊢
  omega

theorem parsed_checked_physical_prefix (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareCheckedPhysicalWithRows parsed.1.2.game.input
      parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).2 steps ≤
        borrowed+BinaryPRGPromiseLifetime.envelope bits.length (bits.length+2)+
          BinaryPRGNumericalPreparationLifetime.envelope bits.length (bits.length+2)+
          2*(PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40)+256 ∧
      framePeak ((prepareCheckedPhysicalWithRows parsed.1.2.game.input
        parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).2.take steps) ≤
        BinaryPRGPromiseLifetime.envelope bits.length (bits.length+2)+
          BinaryPRGNumericalPreparationLifetime.envelope bits.length (bits.length+2)+
          2*(PRGPhysicalArrayInterface.preparationBound bits.length+2*bits.length+40)+256 := by
  simpa only [Nat.add_assoc] using BinaryPRGHeapTraceUsage.all_prefix _ _
    (parsed_checked_physical_usage bits parsed h) borrowed steps

end Blotto.BinaryPRGCheckedPhysicalPreparationLifetime
