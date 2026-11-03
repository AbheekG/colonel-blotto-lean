import Blotto.BinaryTerminalPhysicalAllowanceSeed
import Blotto.BinaryTerminalPhysicalFullRawLifetime

/-! A complete raw request/seed/output runner consumes the encoded builder
allowance route. The charge field is retained cache-prefix source work, not
a complete runtime price. The enlarged trace covers all selected producers. -/

namespace Blotto.BinaryTerminalPhysicalAllowanceRaw
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPhysicalHeapAllowanceInitial RationalLottoResourceSystem
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryTerminalPhysicalAllowanceSeed (calculatorTrace calculatorWork prefixWork
  polynomial_with_frame_overhead)
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- A proof observer; the raw producer does not calculate this trace again. -/
def rawCalculatorTrace (rich : Bool) (frame : List Bool) : Trace :=
  (((BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1.map
    (fun parsed => calculatorTrace parsed.1 rich)).getD [])

def seedCharge (request : PhysicalRequest) (rich : Bool) (seed : List Bool) : ℕ :=
  (((BinaryPRGBooleanSeedBlocks.readWithTrace request.2.logical seed).1.map
    (fun tapes => prefixWork request
      (BinaryWordStoreLifetime.prepareWithTrace tapes.choice.bits).1 rich+
      calculatorWork request rich)).getD 0)

/-- The previous selected cache-prefix charge plus calculator work on the
reached accepted path, and zero before the cache-prefix path is entered. -/
def carriedCharge (rich : Bool) (frame seed : List Bool) : ℕ :=
  (((BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1.map
    (fun parsed => if parsed.2 = [] then seedCharge parsed.1 rich seed else 0)).getD 0)

def run (rich : Bool) (frame seed : List Bool) :
    ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => (((none,[]),wrap 16 2 [decoded.2]),0)
  | some parsed =>
      if parsed.2 = [] then
        let output := BinaryTerminalPhysicalAllowanceSeed.run frame parsed hParsed rich seed
        ((output.1.1,wrap 32 2 [decoded.2,output.1.2]),output.2)
      else (((none,[]),wrap 24 2 [decoded.2]),0)

theorem reference_none (rich : Bool) (frame seed : List Bool)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed =
      (none,wrap 16 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) := by
  unfold BinaryTerminalPhysicalFullRawLifetime.runWithTrace
  dsimp only
  split
  · rfl
  · rename_i parsed hSome
    rw [hRead] at hSome
    cases hSome

theorem reference_accept (rich : Bool) (frame seed : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed =
      ((BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace frame parsed hRead rich seed).1,
        wrap 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace frame parsed hRead rich seed).2]) := by
  unfold BinaryTerminalPhysicalFullRawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_left hTail]

theorem reference_tail (rich : Bool) (frame seed : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed =
      (none,wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) := by
  unfold BinaryTerminalPhysicalFullRawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_right hTail]

theorem run_data (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).1.1.1 =
      (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).1 := by
  unfold run
  dsimp only
  split
  · rename_i hNone
    rw [reference_none rich frame seed hNone]
  · rename_i parsed hParsed
    split
    · rename_i hTail
      rw [reference_accept rich frame seed parsed hParsed hTail]
      exact BinaryTerminalPhysicalAllowanceSeed.run_data frame parsed hParsed rich seed
    · rename_i hTail
      rw [reference_tail rich frame seed parsed hParsed hTail]

theorem run_carried_total_work (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).2+BinaryBigEndian.littleValue (run rich frame seed).1.1.2 =
      carriedCharge rich frame seed := by
  unfold run carriedCharge
  dsimp only
  split
  · rename_i hNone
    rw [hNone]
    rfl
  · rename_i parsed hParsed
    simp only [hParsed,Option.map_some,Option.getD_some]
    split
    · exact BinaryTerminalPhysicalAllowanceSeed.run_carried_total_work
        frame parsed hParsed rich seed
    · rfl

theorem run_trace_delta (rich : Bool) (frame seed : List Bool) :
    BinaryPRGHeapPrimitiveLifetime.cells (run rich frame seed).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).2+
          32+BinaryPRGHeapPrimitiveLifetime.cells (rawCalculatorTrace rich frame) ∧
      framePeak (run rich frame seed).1.2 ≤
        framePeak (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).2+
          framePeak (rawCalculatorTrace rich frame)+30 := by
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  unfold run
  dsimp only
  split
  · rename_i hNone
    rw [reference_none rich frame seed hNone]
    simp only [rawCalculatorTrace,hNone,Option.map_none,Option.getD_none]
    change BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [decoded.2]) ≤
        BinaryPRGHeapPrimitiveLifetime.cells (wrap 16 2 [decoded.2])+
          32+BinaryPRGHeapPrimitiveLifetime.cells [] ∧
      framePeak (wrap 16 2 [decoded.2]) ≤ framePeak (wrap 16 2 [decoded.2])+framePeak []+30
    exact ⟨by omega,by omega⟩
  · rename_i parsed hParsed
    simp only [rawCalculatorTrace,hParsed,Option.map_some,Option.getD_some]
    split
    · rename_i hTail
      rw [reference_accept rich frame seed parsed hParsed hTail]
      let before := BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
        frame parsed hParsed rich seed
      let after := BinaryTerminalPhysicalAllowanceSeed.run frame parsed hParsed rich seed
      have hs := BinaryTerminalPhysicalAllowanceSeed.run_trace_delta
        frame parsed hParsed rich seed
      have hc : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
          BinaryPRGHeapPrimitiveLifetime.cells before.2+
            (32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich)) := by
        simpa only [before,after,Nat.add_assoc] using hs.1
      have hf : framePeak after.1.2 ≤
          framePeak before.2+(framePeak (calculatorTrace parsed.1 rich)+28) := by
        simpa only [before,after,Nat.add_assoc] using hs.2
      have hw := wrap_second_delta 32 2 decoded.2 before.2 after.1.2
        (32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich))
        (framePeak (calculatorTrace parsed.1 rich)+28) hc hf
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [decoded.2,after.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [decoded.2,before.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
        framePeak (wrap 32 2 [decoded.2,after.1.2]) ≤
          framePeak (wrap 32 2 [decoded.2,before.2])+framePeak (calculatorTrace parsed.1 rich)+30
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩
    · rename_i hTail
      rw [reference_tail rich frame seed parsed hParsed hTail]
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [decoded.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [decoded.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
        framePeak (wrap 24 2 [decoded.2]) ≤
          framePeak (wrap 24 2 [decoded.2])+framePeak (calculatorTrace parsed.1 rich)+30
      exact ⟨by omega,by omega⟩

theorem run_usage (rich : Bool) (frame seed : List Bool) :
    usage (run rich frame seed).1.2 ≤
      usage (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).2+
        usage (rawCalculatorTrace rich frame)+62 := by
  have h := run_trace_delta rich frame seed
  unfold usage
  omega

theorem rawCalculatorTrace_polynomial : ∃ C d : ℕ,
    ∀ (rich : Bool) (frame : List Bool),
      usage (rawCalculatorTrace rich frame) ≤ C*(frame.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceSeed.calculatorTrace_polynomial
  refine ⟨C,d,?_⟩
  intro rich frame
  unfold rawCalculatorTrace
  cases h : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 with
  | none =>
      simp only [Option.map_none,Option.getD_none]
      exact Nat.zero_le _
  | some parsed => exact hBound frame parsed h rich

theorem run_request (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).1.1.1 = BinaryPRGRequest.run rich frame seed := by
  rw [run_data]
  exact BinaryTerminalPhysicalFullRawLifetime.runWithTrace_request rich frame seed

theorem returned_budget (rich : Bool) (frame seed bytes : List Bool)
    (h : (run rich frame seed).1.1.1 = some bytes) :
    ∃ parsed : Σ n,BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1,parsed.2.source⟩ : Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) bytes := by
  rw [run_data] at h
  exact BinaryTerminalPhysicalFullRawLifetime.returned_budget rich frame seed bytes h

theorem run_ofFn (frame : List Bool) (parsed : PhysicalRequest)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some (parsed,[]))
    (rich : Bool)
    (bits : Fin (sampleBitBudget parsed.1 parsed.2.logical.request.precision) → Bool) :
    (run rich frame (List.ofFn bits)).1.1.1 =
      some (parsed.2.logical.request.output rich bits) := by
  rw [run_data]
  exact BinaryTerminalPhysicalFullRawLifetime.runWithTrace_ofFn frame parsed hRead rich bits

theorem uniform_carried_work : ∃ C d : ℕ,
    ∀ (rich : Bool) (frame seed : List Bool),
      (run rich frame seed).2+BinaryBigEndian.littleValue (run rich frame seed).1.1.2 ≤
        C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceSeed.accepted_uniform_carried_work
  refine ⟨C,d,?_⟩
  intro rich frame seed
  unfold run
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hParsed
    split
    · exact hBound frame parsed hParsed rich seed
    · exact Nat.zero_le _

theorem uniform_usage : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool),
    usage (run rich frame seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalFullRawLifetime.uniform_usage
  obtain ⟨P,e,hCalc⟩ := rawCalculatorTrace_polynomial
  refine ⟨C+P*3^e+62,max d e,?_⟩
  intro rich frame seed
  exact polynomial_with_frame_overhead _ _ _ _ 62 C P d e
    (hOld rich frame seed) (hCalc rich frame) (run_usage rich frame seed)

theorem uniform_all_prefix : ∃ C d : ℕ,
    ∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
      let B := C*(frame.length+1)^d
      retainedHeap (borrowed+frame.length+seed.length) (run rich frame seed).1.2 steps ≤
          borrowed+frame.length+seed.length+B ∧
        framePeak ((run rich frame seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := uniform_usage
  refine ⟨C,d,?_⟩
  intro rich frame seed borrowed steps
  exact all_prefix _ _ (hUsage rich frame seed) (borrowed+frame.length+seed.length) steps

end Blotto.BinaryTerminalPhysicalAllowanceRaw
