import Blotto.BinaryTerminalPhysicalAllowanceFramed
import Blotto.BinaryTerminalPhysicalSeedOutputLifetime

/-! Validated seed tapes feed the Boolean-allowance physical framing route.
The bit allowance and cache-prefix source-work observer survive validation;
the latter does not price seed preparation or later terminal execution. -/

namespace Blotto.BinaryTerminalPhysicalAllowanceSeed
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPhysicalHeapAllowanceInitial RationalLottoResourceSystem
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Specification observers on the selected physical readback, not extra
readbacks in the producer. -/
def calculatorTrace (request : PhysicalRequest) (rich : Bool) : Trace :=
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    request.2).1.1.getD ([],[])
  calculationTrace words.1 (if rich then words.1 else words.2)

def calculatorWork (request : PhysicalRequest) (rich : Bool) : ℕ :=
  let words := (BinaryPhysicalNumericalReadbackLifetime.readPairWithTraceAndWork
    request.2).1.1.getD ([],[])
  calculationWork words.1 (if rich then words.1 else words.2)

def prefixWork (request : PhysicalRequest) (store : BinarySeedLookupTree.Store)
    (rich : Bool) : ℕ :=
  (BinaryTerminalPhysicalRouteLifetime.runCachedPrefixWithTraceAndWork
    request store rich).2

theorem calculatorTrace_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ rich : Bool, usage (calculatorTrace parsed.1 rich) ≤ C*(frame.length+3)^d :=
  accepted_calculationTrace_polynomial

theorem polynomial_with_frame_overhead (L base extra total K C P d e : ℕ)
    (hBase : base ≤ C*(L+1)^d) (hExtra : extra ≤ P*(L+3)^e)
    (hTotal : total ≤ base+extra+K) :
    total ≤ (C+P*3^e+K)*(L+1)^(max d e) := by
  let X := L+1
  have hX : 0 < X := by dsimp only [X]; omega
  have hSize : L+3 ≤ 3*X := by dsimp only [X]; omega
  have hExtraTop : extra ≤ (P*3^e)*X^e := by
    have hp := Nat.mul_le_mul_left P (Nat.pow_le_pow_left hSize e)
    rw [Nat.mul_pow] at hp
    exact hExtra.trans (hp.trans_eq (by ring))
  have hd := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left (P*3^e)
    (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hOne := Nat.one_le_pow (max d e) X (by omega)
  change base ≤ C*X^d at hBase
  change total ≤ (C+P*3^e+K)*X^(max d e)
  nlinarith only [hTotal,hBase,hExtraTop,hd,he,hOne]

def output (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) : ((List Bool × List Bool) × Trace) × ℕ :=
  let prepared := BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits
  let drawn := BinaryTerminalPhysicalAllowanceFramed.run frame parsed hParsed prepared.1 rich
    parsed.1.2.logical.request.precision blocks.outer blocks.scalar parsed.1.2.logical.header
  (((drawn.1.1.1.1,drawn.1.1.2),wrap 16 2 [prepared.2,drawn.1.2]),drawn.2)

theorem output_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    (output frame parsed hParsed rich blocks).1.1.1 =
      (BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace
        frame parsed hParsed rich blocks).1 := by
  simp only [output,BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace,
    BinaryTerminalPhysicalAllowanceFramed.run_data]

theorem output_carried_total_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    (output frame parsed hParsed rich blocks).2+
      BinaryBigEndian.littleValue (output frame parsed hParsed rich blocks).1.1.2 =
      prefixWork parsed.1 (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich+
        calculatorWork parsed.1 rich :=
  BinaryTerminalPhysicalAllowanceFramed.run_carried_total_work frame parsed hParsed
    (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich
    parsed.1.2.logical.request.precision blocks.outer blocks.scalar parsed.1.2.logical.header

theorem output_trace_delta (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    BinaryPRGHeapPrimitiveLifetime.cells (output frame parsed hParsed rich blocks).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace
            frame parsed hParsed rich blocks).2+
          32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
      framePeak (output frame parsed hParsed rich blocks).1.2 ≤
        framePeak (BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace
          frame parsed hParsed rich blocks).2+framePeak (calculatorTrace parsed.1 rich)+26 := by
  let prepared := BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits
  let before := BinaryTerminalPhysicalFramedLifetime.runWithTrace frame parsed hParsed
    prepared.1 rich parsed.1.2.logical.request.precision blocks.outer blocks.scalar
    parsed.1.2.logical.header
  let after := BinaryTerminalPhysicalAllowanceFramed.run frame parsed hParsed
    prepared.1 rich parsed.1.2.logical.request.precision blocks.outer blocks.scalar
    parsed.1.2.logical.header
  have h := BinaryTerminalPhysicalAllowanceFramed.run_trace_delta frame parsed hParsed
    prepared.1 rich parsed.1.2.logical.request.precision blocks.outer blocks.scalar
    parsed.1.2.logical.header
  change BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.2+32+
        BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
    framePeak after.1.2 ≤ framePeak before.2+framePeak (calculatorTrace parsed.1 rich)+24 at h
  have hc : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
      BinaryPRGHeapPrimitiveLifetime.cells before.2+
        (32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich)) := by omega
  have hf : framePeak after.1.2 ≤
      framePeak before.2+(framePeak (calculatorTrace parsed.1 rich)+24) := by omega
  have hw := wrap_second_delta 16 2 prepared.2 before.2 after.1.2
    (32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich))
    (framePeak (calculatorTrace parsed.1 rich)+24) hc hf
  change BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [prepared.2,after.1.2]) ≤
      BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [prepared.2,before.2])+
        32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
    framePeak (wrap 16 2 [prepared.2,after.1.2]) ≤
      framePeak (wrap 16 2 [prepared.2,before.2])+framePeak (calculatorTrace parsed.1 rich)+26
  exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

theorem output_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    usage (output frame parsed hParsed rich blocks).1.2 ≤
      usage (BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace
        frame parsed hParsed rich blocks).2+usage (calculatorTrace parsed.1 rich)+58 := by
  have h := output_trace_delta frame parsed hParsed rich blocks
  unfold usage
  omega

theorem accepted_store_size (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    let store := (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1
    frame.length+store.width+store.cap.value+3 ≤ 10000*(frame.length+1) := by
  let N := blocks.choice.bits.length
  let store := (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hAcc : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hSeed := BinaryPRGSeedRequestBound.read_seedCount_bound
    frame (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hAcc
  have hN : N ≤ 8*frame.length+3025 := by
    have hChoice := blocks.choice.size
    change N = coinBitBudget parsed.1.1 parsed.1.2.logical.request.precision at hChoice
    change sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision ≤
      BinaryPRGSeedRequestBound.seedCountBound frame.length at hSeed
    unfold sampleBitBudget innerBitBudget BinaryPRGSeedRequestBound.seedCountBound at hSeed
    omega
  have hE : store = BinarySeedLookupTree.prepare blocks.choice.bits :=
    BinaryWordStoreLifetime.prepareWithTrace_erases blocks.choice.bits
  have hWidth : store.width ≤ N+1 := by
    rw [hE]
    exact (BinarySeedLookupTree.prepare_width_bound blocks.choice.bits).trans
      (BinaryPRGSeedOutputLifetimePolynomial.wordWidth_le N)
  have hCap : store.cap.value = N := by rw [hE,BinarySeedLookupTree.prepare_cap]
  change frame.length+store.width+store.cap.value+3 ≤ 10000*(frame.length+1)
  omega

theorem output_uniform_carried_work : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
        parsed.1.2.logical.request.precision),
      (output frame parsed hParsed rich blocks).2+
        BinaryBigEndian.littleValue (output frame parsed hParsed rich blocks).1.1.2 ≤
        C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceFramed.accepted_uniform_carried_work
  refine ⟨C*10000^d,d,?_⟩
  intro frame parsed hParsed rich blocks
  have h := hBound frame parsed hParsed
    (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich
    parsed.1.2.logical.request.precision blocks.outer blocks.scalar parsed.1.2.logical.header
  have hp := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (accepted_store_size frame parsed hParsed blocks) d)
  rw [Nat.mul_pow] at hp
  exact h.trans (hp.trans_eq (by ring))

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let blocks := BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed
  match blocks.1 with
  | none => (((none,[]),wrap 16 2 [blocks.2]),0)
  | some tapes =>
      let drawn := output frame parsed hParsed rich tapes
      (((some drawn.1.1.1,drawn.1.1.2),wrap 32 2 [blocks.2,drawn.1.2]),drawn.2)

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1.1 =
      (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace frame parsed hParsed rich seed).1 := by
  unfold run BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
  dsimp only
  cases h : (BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed).1
  · rfl
  · exact congrArg some (output_data frame parsed hParsed rich _)

theorem run_carried_total_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 =
      (((BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed).1.map
        (fun tapes => prefixWork parsed.1
          (BinaryWordStoreLifetime.prepareWithTrace tapes.choice.bits).1 rich+
          calculatorWork parsed.1 rich)).getD 0) := by
  unfold run
  dsimp only
  cases h : (BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed).1 with
  | none => rfl
  | some tapes =>
      exact output_carried_total_work frame parsed hParsed rich tapes

theorem run_trace_delta (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    BinaryPRGHeapPrimitiveLifetime.cells (run frame parsed hParsed rich seed).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
            frame parsed hParsed rich seed).2+
          32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
      framePeak (run frame parsed hParsed rich seed).1.2 ≤
        framePeak (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
          frame parsed hParsed rich seed).2+framePeak (calculatorTrace parsed.1 rich)+28 := by
  let blocks := BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed
  unfold run BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
  dsimp only
  cases h : blocks.1 with
  | none =>
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [blocks.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [blocks.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
        framePeak (wrap 16 2 [blocks.2]) ≤
          framePeak (wrap 16 2 [blocks.2])+framePeak (calculatorTrace parsed.1 rich)+28
      exact ⟨by omega,by omega⟩
  | some tapes =>
      let before := BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace
        frame parsed hParsed rich tapes
      let after := output frame parsed hParsed rich tapes
      have ho := output_trace_delta frame parsed hParsed rich tapes
      have hc : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
          BinaryPRGHeapPrimitiveLifetime.cells before.2+
            (32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich)) := by
        simpa only [before,after,Nat.add_assoc] using ho.1
      have hf : framePeak after.1.2 ≤
          framePeak before.2+(framePeak (calculatorTrace parsed.1 rich)+26) := by
        simpa only [before,after,Nat.add_assoc] using ho.2
      have hw := wrap_second_delta 32 2 blocks.2 before.2 after.1.2
        (32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich))
        (framePeak (calculatorTrace parsed.1 rich)+26) hc hf
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [blocks.2,after.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [blocks.2,before.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
        framePeak (wrap 32 2 [blocks.2,after.1.2]) ≤
          framePeak (wrap 32 2 [blocks.2,before.2])+framePeak (calculatorTrace parsed.1 rich)+28
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩

theorem run_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    usage (run frame parsed hParsed rich seed).1.2 ≤
      usage (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
        frame parsed hParsed rich seed).2+usage (calculatorTrace parsed.1 rich)+60 := by
  have h := run_trace_delta frame parsed hParsed rich seed
  unfold usage
  omega

theorem accepted_request (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1.1 =
      (RationalPRGBinaryRequest.seedTable
        (sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision) seed).map
        (fun table => parsed.1.2.logical.request.output rich table.read) := by
  rw [run_data]
  exact BinaryTerminalPhysicalSeedOutputLifetime.accepted_request
    frame parsed hParsed rich seed

theorem accepted_reject (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1.1 = none ↔
      (BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.logical.request.precision seed).1 = none := by
  rw [run_data]
  exact BinaryTerminalPhysicalSeedOutputLifetime.accepted_reject
    frame parsed hParsed rich seed

theorem accepted_uniform_carried_work : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool),
      (run frame parsed hParsed rich seed).2+
        BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 ≤
        C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := output_uniform_carried_work
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich seed
  unfold run
  dsimp only
  cases h : (BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed).1 with
  | none => exact Nat.zero_le _
  | some tapes => exact hBound frame parsed hParsed rich tapes

theorem accepted_uniform_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool),
      usage (run frame parsed hParsed rich seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalSeedOutputLifetime.accepted_uniform_polynomial
  obtain ⟨P,e,hCalc⟩ := calculatorTrace_polynomial
  refine ⟨C+P*3^e+60,max d e,?_⟩
  intro frame parsed hParsed rich seed
  exact polynomial_with_frame_overhead _ _ _ _ 60 C P d e
    (hOld frame parsed hParsed rich seed) (hCalc frame parsed hParsed rich)
    (run_usage frame parsed hParsed rich seed)

theorem accepted_all_prefix : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool) (borrowed steps : ℕ),
      let B := C*(frame.length+1)^d
      retainedHeap (borrowed+frame.length+seed.length)
          (run frame parsed hParsed rich seed).1.2 steps ≤
          borrowed+frame.length+seed.length+B ∧
        framePeak ((run frame parsed hParsed rich seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := accepted_uniform_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich seed borrowed steps
  exact all_prefix _ _ (hUsage frame parsed hParsed rich seed)
    (borrowed+frame.length+seed.length) steps

end Blotto.BinaryTerminalPhysicalAllowanceSeed
