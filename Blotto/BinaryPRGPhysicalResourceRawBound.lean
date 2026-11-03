import Blotto.BinaryPRGPhysicalResourceInitialLifetime

/-! Original-frame bounds for the physical numerical stores used by the
initial resource scan. The scan is parallel to the selected sampler path. -/
namespace Blotto.BinaryPRGPhysicalResourceRawBound
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGPreparation BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalResourceInitialLifetime
set_option autoImplicit false
set_option maxHeartbeats 3000000

private theorem castStore_caps {m n : ℕ} (h : m = n)
    (store : BinaryWordObjectArray.Store m) :
    (BinaryPRGCheckedPhysicalPreparationLifetime.castStore h store).heap.tape.length =
        store.heap.tape.length ∧
      (BinaryPRGCheckedPhysicalPreparationLifetime.castStore h store).slots.length =
        store.slots.length := by
  cases h
  exact ⟨rfl,rfl⟩

private theorem fixedPhysical_caps (length n : ℕ)
    (entries : List (SignedWord × Trace)) (hEntries : entries.length = n)
    (hn : n ≤ length)
    (hWidth : ∀ word ∈ BinaryPRGNumericalPhysicalEntries.words entries,
      width word ≤ 9*length+22) :
    (BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical n entries hEntries).1.heap.tape.length ≤
        PRGPhysicalArrayInterface.heapCap length ∧
      (BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical n entries hEntries).1.slots.length ≤
        PRGPhysicalArrayInterface.slotsCap length := by
  have hCaps := BinaryPRGNumericalPhysicalMapLifetime.physical_store_caps
    length n entries hEntries hn hWidth
  unfold BinaryPRGCheckedPhysicalPreparationLifetime.fixedPhysical
  dsimp only
  have hCast := castStore_caps
    (show (BinaryLifetimeArray.mapDirectWithTrace Prod.fst entries).1.length = n by
      rw [BinaryPRGNumericalPhysicalMapLifetime.projected_trace_words,
        BinaryPRGNumericalPhysicalEntries.words_length,hEntries])
    (BinaryPRGNumericalPhysicalMapLifetime.prepareWithTrace entries).1
  omega

private theorem parsed_prepared_caps (frame : List Bool)
    (game : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hGame : (BinaryPRGGameFrameLifetime.readWithTrace frame).1 = some game) :
    let prepared := (BinaryPRGCheckedPhysicalPreparationLifetime.prepareWithRowsPhysical
      game.1.2.game.input game.1.2.rows game.1.2.rows_readback).1
    (prepared.lengthStore.heap.tape.length ≤ PRGPhysicalArrayInterface.heapCap frame.length ∧
      prepared.lengthStore.slots.length ≤ PRGPhysicalArrayInterface.slotsCap frame.length) ∧
    (prepared.poorStore.heap.tape.length ≤ PRGPhysicalArrayInterface.heapCap frame.length ∧
      prepared.poorStore.slots.length ≤ PRGPhysicalArrayInterface.slotsCap frame.length) := by
  dsimp only
  let input := game.1.2.game.input
  let rows := game.1.2.rows
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  have hSizes := BinaryPRGCheckedGameLifetime.parsed_sizes frame game hGame
  have hLength : lengthEntries.length = game.1.1 := by
    dsimp only [lengthEntries]
    rw [BinaryLifetimeArray.mapDirect_length,game.1.2.rows_length]
  have hPoor : poorEntries.length = game.1.1 := by
    dsimp only [poorEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hLength]
  have hWidths := BinaryPRGNumericalPhysicalEntries.selected_widths input
    game.1.2.game.canonical rows game.1.2.rows_readback
  dsimp only [input,rows,ratio,lengthEntries,poorEntries] at hWidths
  have hLengthWidth : ∀ word ∈ BinaryPRGNumericalPhysicalEntries.words lengthEntries,
      width word ≤ 9*frame.length+22 := by
    intro word hw
    have h := hWidths.1 word hw
    omega
  have hPoorWidth : ∀ word ∈ BinaryPRGNumericalPhysicalEntries.words poorEntries,
      width word ≤ 9*frame.length+22 := by
    intro word hw
    have h := hWidths.2 word hw
    omega
  have hFirst := fixedPhysical_caps frame.length game.1.1 lengthEntries hLength
    hSizes.1 hLengthWidth
  have hSecond := fixedPhysical_caps frame.length game.1.1 poorEntries hPoor
    hSizes.1 hPoorWidth
  simpa only [BinaryPRGCheckedPhysicalPreparationLifetime.prepareWithRowsPhysical]
    using And.intro hFirst hSecond

private theorem checked_result_caps (frame : List Bool)
    (game : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hGame : (BinaryPRGGameFrameLifetime.readWithTrace frame).1 = some game)
    (result : {p : BinaryPRGCheckedPhysicalPreparationLifetime.PreparedPhysical game.1.1 //
      p.numerical.Valid})
    (hResult : (BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
      game.1.2.game.input game.1.2.game.canonical
      game.1.2.rows game.1.2.rows_readback).1 = some result) :
    (result.1.lengthStore.heap.tape.length ≤ PRGPhysicalArrayInterface.heapCap frame.length ∧
      result.1.lengthStore.slots.length ≤ PRGPhysicalArrayInterface.slotsCap frame.length) ∧
    (result.1.poorStore.heap.tape.length ≤ PRGPhysicalArrayInterface.heapCap frame.length ∧
      result.1.poorStore.slots.length ≤ PRGPhysicalArrayInterface.slotsCap frame.length) := by
  unfold BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows at hResult
  by_cases hCheck : (BinaryPRGPromiseLifetime.checkRowsWithTrace
      game.1.2.game.input game.1.2.rows).1 = true
  · simp only [hCheck,dite_true,Option.some.injEq] at hResult
    subst result
    exact parsed_prepared_caps frame game hGame
  · simp only [hCheck] at hResult
    cases hResult

private theorem returned_game_caps (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalCheckedGameLifetime.Checked n) × List Bool)
    (hParsed : (BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).1 = some parsed) :
    (parsed.1.2.prepared.1.lengthStore.heap.tape.length ≤
        PRGPhysicalArrayInterface.heapCap frame.length ∧
      parsed.1.2.prepared.1.lengthStore.slots.length ≤
        PRGPhysicalArrayInterface.slotsCap frame.length) ∧
    (parsed.1.2.prepared.1.poorStore.heap.tape.length ≤
        PRGPhysicalArrayInterface.heapCap frame.length ∧
      parsed.1.2.prepared.1.poorStore.slots.length ≤
        PRGPhysicalArrayInterface.slotsCap frame.length) := by
  unfold BinaryPRGPhysicalCheckedGameLifetime.readWithTrace at hParsed
  cases hGame : (BinaryPRGGameFrameLifetime.readWithTrace frame).1 with
  | none => simp only [hGame] at hParsed; cases hParsed
  | some game =>
      simp only [hGame] at hParsed
      cases hChecked : (BinaryPRGCheckedPhysicalPreparationLifetime.prepareCheckedPhysicalWithRows
        game.1.2.game.input game.1.2.game.canonical
        game.1.2.rows game.1.2.rows_readback).1 with
      | none => simp only [hChecked,Option.map_none] at hParsed; cases hParsed
      | some result =>
          simp only [hChecked,Option.map_some,Option.some.injEq] at hParsed
          subst parsed
          exact checked_result_caps frame game hGame result hChecked

theorem returned_raw_caps (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (parsed.1.2.physical.lengthStore.heap.tape.length ≤
        PRGPhysicalArrayInterface.heapCap frame.length ∧
      parsed.1.2.physical.lengthStore.slots.length ≤
        PRGPhysicalArrayInterface.slotsCap frame.length) ∧
    (parsed.1.2.physical.poorStore.heap.tape.length ≤
        PRGPhysicalArrayInterface.heapCap frame.length ∧
      parsed.1.2.physical.poorStore.slots.length ≤
        PRGPhysicalArrayInterface.slotsCap frame.length) := by
  unfold BinaryPRGPhysicalRawRequestLifetime.readWithTrace at hParsed
  cases hGame : (BinaryPRGPhysicalCheckedGameLifetime.readWithTrace frame).1 with
  | none => simp only [hGame] at hParsed; cases hParsed
  | some game =>
      simp only [hGame] at hParsed
      cases hAccuracy : (BinaryAccuracyLifetime.readWithTrace game.2).1 with
      | none => simp only [hAccuracy] at hParsed; cases hParsed
      | some selected =>
          simp only [hAccuracy,Option.some.injEq] at hParsed
          subst parsed
          exact returned_game_caps frame game hGame

private theorem store_readEnvelope_raw {n length : ℕ}
    (store : BinaryWordObjectArray.Store n)
    (hHeap : store.heap.tape.length ≤ PRGPhysicalArrayInterface.heapCap length)
    (hSlots : store.slots.length ≤ PRGPhysicalArrayInterface.slotsCap length)
    (width : ℕ) (hWidth : width ≤ length+1) :
    BinaryWordObjectArrayAccess.envelope store width ≤
      PRGPhysicalArrayInterface.readEnvelope length := by
  have hDepth := (PRGPhysicalArrayInterface.wordWidth_le store.heap.tape.length).trans
    (Nat.add_le_add_right hHeap 1)
  unfold BinaryWordObjectArrayAccess.envelope BinaryWordObjectArrayAccess.heapReadEnvelope
    PRGPhysicalArrayInterface.readEnvelope BinaryReferenceVector.readBound
    BinaryPRGWordStoreHeapMachine.readBound BinaryPRGWordStoreHeapMachine.skipBound
  gcongr

private theorem returned_raw_dimension (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    parsed.1.1 ≤ frame.length := by
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hRead : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  exact BinaryPRGSeedRequestBound.read_dimension_bound frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRead

theorem returned_lookupEnvelope_raw (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    lookupEnvelope parsed.1.2 rich (binaryWordWidth parsed.1.1) ≤
      2*PRGPhysicalArrayInterface.readEnvelope frame.length+24 := by
  have hCaps := returned_raw_caps frame parsed hParsed
  have hn := returned_raw_dimension frame parsed hParsed
  have hWidth : binaryWordWidth parsed.1.1 ≤ frame.length+1 :=
    (PRGPhysicalArrayInterface.wordWidth_le parsed.1.1).trans (Nat.add_le_add_right hn 1)
  have hLength := store_readEnvelope_raw parsed.1.2.physical.lengthStore
    hCaps.1.1 hCaps.1.2 _ hWidth
  cases rich with
  | false =>
      have hPoor := store_readEnvelope_raw parsed.1.2.physical.poorStore
        hCaps.2.1 hCaps.2.2 _ hWidth
      unfold lookupEnvelope resourceStore
      simp only [Bool.false_eq_true,ite_false]
      omega
  | true =>
      unfold lookupEnvelope resourceStore
      simp only [ite_true]
      omega

def rawScanEnvelope (length : ℕ) : ℕ :=
  32*length+16+length*(2*PRGPhysicalArrayInterface.readEnvelope length+24)+
    32*(length+1)+40

theorem readEnvelope_polynomial (length : ℕ) :
    PRGPhysicalArrayInterface.readEnvelope length ≤
      600000000*(length+3)^6 := by
  let x := length+3
  have hx : 1 ≤ x := by dsimp [x]; omega
  have h1 : 1 ≤ x^2 := Nat.one_le_pow _ _ hx
  have h2 : x ≤ x^2 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right hx (show (1:ℕ) ≤ 2 by omega))
  have h3 : x ≤ x^3 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right hx (show (1:ℕ) ≤ 3 by omega))
  have h4 : x^2 ≤ x^4 := Nat.pow_le_pow_right hx (by omega)
  have h5 : x^4 ≤ x^6 := Nat.pow_le_pow_right hx (by omega)
  have h6 : 1 ≤ x^6 := Nat.one_le_pow _ _ hx
  have hHeap : PRGPhysicalArrayInterface.heapCap length ≤ 128*x^2 := by
    unfold PRGPhysicalArrayInterface.heapCap
    dsimp [x]
    nlinarith
  have hSlots : PRGPhysicalArrayInterface.slotsCap length ≤ 259*x^3 := by
    unfold PRGPhysicalArrayInterface.slotsCap
    calc
      length*(2*(PRGPhysicalArrayInterface.heapCap length+1)+1) ≤
          x*(2*(128*x^2+1)+1) := by gcongr; dsimp [x]; omega
      _ ≤ 259*x^3 := by nlinarith
  have hRefA : PRGPhysicalArrayInterface.slotsCap length+1 ≤ 260*x^3 := by omega
  have hRefB : PRGPhysicalArrayInterface.slotsCap length+length+3 ≤ 260*x^3 := by
    have hEq : length+3 = x := rfl
    omega
  have hRefB' : PRGPhysicalArrayInterface.slotsCap length+(length+1)+2 ≤
      260*x^3 := by omega
  have hReference : BinaryReferenceVector.readBound
      (PRGPhysicalArrayInterface.slotsCap length) (length+1) ≤ 8652800*x^6 := by
    unfold BinaryReferenceVector.readBound
    calc
      128*(PRGPhysicalArrayInterface.slotsCap length+1)*
          (PRGPhysicalArrayInterface.slotsCap length+(length+1)+2) ≤
          128*(260*x^3)*(260*x^3) := by gcongr
      _ = 8652800*x^6 := by ring
  have hHeapA : PRGPhysicalArrayInterface.heapCap length+1 ≤ 129*x^2 := by omega
  have hHeapB : 5*(PRGPhysicalArrayInterface.heapCap length+2)+4 ≤ 654*x^2 := by omega
  have hHeapC : 8*PRGPhysicalArrayInterface.heapCap length+10 ≤ 1034*x^2 := by omega
  have hRead : BinaryPRGWordStoreHeapMachine.readBound
      (PRGPhysicalArrayInterface.heapCap length)
      (PRGPhysicalArrayInterface.heapCap length+1) ≤ 85400*x^4 := by
    unfold BinaryPRGWordStoreHeapMachine.readBound
      BinaryPRGWordStoreHeapMachine.skipBound
    have hProduct :
        (PRGPhysicalArrayInterface.heapCap length+1)*
          (5*(PRGPhysicalArrayInterface.heapCap length+2)+4) ≤
          (129*x^2)*(654*x^2) := Nat.mul_le_mul hHeapA hHeapB
    nlinarith
  have hProduct : PRGPhysicalArrayInterface.heapCap length*
      (PRGPhysicalArrayInterface.heapCap length+1) ≤ 16512*x^4 := by
    calc
      PRGPhysicalArrayInterface.heapCap length*
          (PRGPhysicalArrayInterface.heapCap length+1) ≤
          (128*x^2)*(129*x^2) := Nat.mul_le_mul hHeap hHeapA
      _ = 16512*x^4 := by ring
  have hTail : 2*PRGPhysicalArrayInterface.heapCap length+5 ≤ 261*x^4 := by
    nlinarith
  change PRGPhysicalArrayInterface.readEnvelope length ≤ 600000000*x^6
  unfold PRGPhysicalArrayInterface.readEnvelope
  nlinarith [hReference,hRead,hProduct,hTail,h5,h6]

theorem rawScanEnvelope_polynomial (length : ℕ) :
    rawScanEnvelope length ≤ 2000000000*(length+3)^7 := by
  let x := length+3
  have hx : 1 ≤ x := by dsimp [x]; omega
  have hPower : x ≤ x^7 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right hx (show (1:ℕ) ≤ 7 by omega))
  have hOne : 1 ≤ x^7 := Nat.one_le_pow _ _ hx
  have hRead := readEnvelope_polynomial length
  change PRGPhysicalArrayInterface.readEnvelope length ≤ 600000000*x^6 at hRead
  have hProduct : length*(2*PRGPhysicalArrayInterface.readEnvelope length+24) ≤
      x*(1200000000*x^6+24) := by
    apply Nat.mul_le_mul
    · dsimp [x]; omega
    · omega
  change rawScanEnvelope length ≤ 2000000000*x^7
  unfold rawScanEnvelope
  have hLength : length ≤ x := by dsimp [x]; omega
  calc
    32*length+16+length*(2*PRGPhysicalArrayInterface.readEnvelope length+24)+
        32*(length+1)+40 ≤
        32*x+16+x*(1200000000*x^6+24)+32*(x+1)+40 := by omega
    _ = 1200000000*x^7+88*x+88 := by ring
    _ ≤ 2000000000*x^7 := by omega

theorem initialUniformEnvelope_raw (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    initialUniformEnvelope parsed.1.2 rich ≤ rawScanEnvelope frame.length := by
  have hn := returned_raw_dimension frame parsed hParsed
  have hLookup := returned_lookupEnvelope_raw frame parsed hParsed rich
  have hProduct : parsed.1.1 * lookupEnvelope parsed.1.2 rich (binaryWordWidth parsed.1.1) ≤
      frame.length * (2*PRGPhysicalArrayInterface.readEnvelope frame.length+24) :=
    Nat.mul_le_mul hn hLookup
  unfold initialUniformEnvelope rawScanEnvelope
  omega

theorem initialScanWithTrace_raw_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    usage (initialScanWithTrace parsed.1.2 rich).2 ≤ rawScanEnvelope frame.length :=
  (initialScanWithTrace_uniform_usage parsed.1.2 rich).trans
    (initialUniformEnvelope_raw frame parsed hParsed rich)

theorem initialScanWithTrace_polynomial_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    usage (initialScanWithTrace parsed.1.2 rich).2 ≤
      2000000000*(frame.length+3)^7 :=
  (initialScanWithTrace_raw_usage frame parsed hParsed rich).trans
    (rawScanEnvelope_polynomial frame.length)

theorem initialScanWithTrace_raw_prefix (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (initialScanWithTrace parsed.1.2 rich).2 steps ≤
        borrowed+rawScanEnvelope frame.length ∧
      framePeak ((initialScanWithTrace parsed.1.2 rich).2.take steps) ≤
        rawScanEnvelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (initialScanWithTrace_raw_usage frame parsed hParsed rich) borrowed steps

theorem resourceWorkWithPhysical_raw_trace_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (N : ℕ) (bits : Fin N → Bool) :
    usage (resourceWorkWithPhysical frame parsed hParsed rich N bits).2 ≤
      rawScanEnvelope frame.length := by
  rw [resourceWorkWithPhysical_trace]
  exact initialScanWithTrace_raw_usage frame parsed hParsed rich

theorem resourceWorkWithPhysical_polynomial_trace_prefix (frame : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (N : ℕ) (bits : Fin N → Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (resourceWorkWithPhysical frame parsed hParsed rich N bits).2 steps ≤
        borrowed+2000000000*(frame.length+3)^7 ∧
      framePeak ((resourceWorkWithPhysical frame parsed hParsed rich N bits).2.take steps) ≤
        2000000000*(frame.length+3)^7 := by
  rw [resourceWorkWithPhysical_trace]
  exact BinaryPRGHeapTraceUsage.all_prefix _ _
    (initialScanWithTrace_polynomial_usage frame parsed hParsed rich) borrowed steps

end Blotto.BinaryPRGPhysicalResourceRawBound
