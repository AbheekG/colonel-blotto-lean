import Blotto.BinaryTerminalPhysicalAllowanceRaw
import Blotto.BinaryTerminalPhysicalFreshRawLifetime
import Blotto.BinaryPRGBooleanFreshPairLifetime

/-! Fresh-bit execution and consecutive player draws use the physical
Boolean-allowance route. Exact bytes, fresh state and call counts are preserved.
The separate natural charge fields carry cache-prefix work only. -/

namespace Blotto.BinaryTerminalPhysicalAllowanceFresh
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPhysicalHeapAllowanceInitial RationalLottoResourceSystem
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryTerminalPhysicalAllowanceSeed (calculatorTrace polynomial_with_frame_overhead)
open BinaryTerminalPhysicalAllowanceRaw (rawCalculatorTrace seedCharge)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem wrap_third_delta (slots frames : ℕ) (first second before after : Trace)
    (A F : ℕ)
    (hCells : BinaryPRGHeapPrimitiveLifetime.cells after ≤
      BinaryPRGHeapPrimitiveLifetime.cells before+A)
    (hFrame : framePeak after ≤ framePeak before+F) :
    BinaryPRGHeapPrimitiveLifetime.cells (wrap slots frames [first,second,after]) ≤
        BinaryPRGHeapPrimitiveLifetime.cells (wrap slots frames [first,second,before])+A ∧
      framePeak (wrap slots frames [first,second,after]) ≤
        framePeak (wrap slots frames [first,second,before])+F+2 := by
  have hNew := framePeak_under 2 after
  have hOld := framePeak_le_under 2 before
  simp only [wrap,combine,BinaryPRGHeapPrimitiveLifetime.cells,
    listCells_append,arraySlots_append,listCells_under,arraySlots_under,
    listCells,arraySlots,framePeak_append,framePeak]
  unfold BinaryPRGHeapPrimitiveLifetime.cells at hCells
  exact ⟨by omega,by omega⟩

def carriedCharge {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : ℕ :=
  (((BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1.map
    (fun parsed => if parsed.2 = [] then
      seedCharge parsed.1 rich (BinaryPRGSeedCountLifetime.generateWithTrace fresh
        parsed.1.2.logical.request state).1.1 else 0)).getD 0)

def run {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((Option (List Bool) × S) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => ((((none,state),[]),wrap 24 2 [decoded.2]),0)
  | some parsed =>
      if parsed.2 = [] then
        let generated := BinaryPRGSeedCountLifetime.generateWithTrace fresh
          parsed.1.2.logical.request state
        let output := BinaryTerminalPhysicalAllowanceSeed.run
          frame parsed hParsed rich generated.1.1
        ((((output.1.1.1,generated.1.2),output.1.1.2),
          wrap 48 2 [decoded.2,generated.2,output.1.2]),output.2)
      else ((((none,state),[]),wrap 32 2 [decoded.2]),0)

theorem reject_none {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    run fresh rich frame state =
      ((((none,state),[]),wrap 24 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]),0) := by
  unfold run
  dsimp only
  split
  · rfl
  · rename_i parsed hSome
    rw [hRead] at hSome
    cases hSome

theorem reject_tail {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    run fresh rich frame state =
      ((((none,state),[]),wrap 32 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]),0) := by
  unfold run
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_right hTail]

theorem reference_none {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh rich frame state =
      ((none,state),wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) := by
  unfold BinaryTerminalPhysicalFreshRawLifetime.runWithTrace
  dsimp only
  split
  · rfl
  · rename_i parsed hSome
    rw [hRead] at hSome
    cases hSome

theorem reference_accept {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    let generated := BinaryPRGSeedCountLifetime.generateWithTrace fresh
      parsed.1.2.logical.request state
    let output := BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
      frame parsed hRead rich generated.1.1
    BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh rich frame state =
      ((output.1,generated.1.2),wrap 48 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,generated.2,output.2]) := by
  unfold BinaryTerminalPhysicalFreshRawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_left hTail]

theorem reference_tail {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh rich frame state =
      ((none,state),wrap 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) := by
  unfold BinaryTerminalPhysicalFreshRawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_right hTail]

theorem run_data {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (run fresh rich frame state).1.1.1 =
      (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh rich frame state).1 := by
  unfold run
  dsimp only
  split
  · rename_i hNone
    rw [reference_none fresh rich frame state hNone]
  · rename_i parsed hParsed
    split
    · rename_i hTail
      rw [reference_accept fresh rich frame state parsed hParsed hTail]
      exact Prod.ext (BinaryTerminalPhysicalAllowanceSeed.run_data frame parsed hParsed
        rich (BinaryPRGSeedCountLifetime.generateWithTrace fresh
          parsed.1.2.logical.request state).1.1) rfl
    · rename_i hTail
      rw [reference_tail fresh rich frame state parsed hParsed hTail]

theorem run_carried_total_work {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (run fresh rich frame state).2+
      BinaryBigEndian.littleValue (run fresh rich frame state).1.1.2 =
      carriedCharge fresh rich frame state := by
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
        frame parsed hParsed rich _
    · rfl

theorem run_counted {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (calls : ℕ) :
    (run (FreshBitSeedLifetime.countedFresh fresh) rich frame (state,calls)).1.1.1 =
      ((run fresh rich frame state).1.1.1.1,
        ((run fresh rich frame state).1.1.1.2,
          calls+BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [run_data,BinaryTerminalPhysicalFreshRawLifetime.runWithTrace_counted]

theorem accepted_returns {S : Type*} (fresh : S → Bool × S)
    (rich : Bool) (frame : List Bool) (parsed : PhysicalRequest)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some (parsed,[]))
    (state : S) :
    ∃ bits : Fin (sampleBitBudget parsed.1 parsed.2.logical.request.precision) → Bool,
      (run fresh rich frame state).1.1.1.1 = some (parsed.2.logical.request.output rich bits) := by
  rw [run_data]
  exact BinaryTerminalPhysicalFreshRawLifetime.accepted_returns fresh rich frame parsed hRead state

theorem returned_budget {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (bytes : List Bool)
    (h : (run fresh rich frame state).1.1.1.1 = some bytes) :
    ∃ parsed : Σ n,BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1,parsed.2.source⟩ : Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) bytes := by
  rw [run_data] at h
  exact BinaryTerminalPhysicalFreshRawLifetime.returned_budget fresh rich frame state bytes h

theorem run_trace_delta {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    BinaryPRGHeapPrimitiveLifetime.cells (run fresh rich frame state).1.2 ≤
        BinaryPRGHeapPrimitiveLifetime.cells
          (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh rich frame state).2+
          32+BinaryPRGHeapPrimitiveLifetime.cells (rawCalculatorTrace rich frame) ∧
      framePeak (run fresh rich frame state).1.2 ≤
        framePeak (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh rich frame state).2+
          framePeak (rawCalculatorTrace rich frame)+30 := by
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  unfold run
  dsimp only
  split
  · rename_i hNone
    rw [reference_none fresh rich frame state hNone]
    simp only [BinaryTerminalPhysicalAllowanceRaw.rawCalculatorTrace,
      hNone,Option.map_none,Option.getD_none]
    change BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [decoded.2]) ≤
        BinaryPRGHeapPrimitiveLifetime.cells (wrap 24 2 [decoded.2])+
          32+BinaryPRGHeapPrimitiveLifetime.cells [] ∧
      framePeak (wrap 24 2 [decoded.2]) ≤ framePeak (wrap 24 2 [decoded.2])+framePeak []+30
    exact ⟨by omega,by omega⟩
  · rename_i parsed hParsed
    simp only [BinaryTerminalPhysicalAllowanceRaw.rawCalculatorTrace,
      hParsed,Option.map_some,Option.getD_some]
    split
    · rename_i hTail
      rw [reference_accept fresh rich frame state parsed hParsed hTail]
      let generated := BinaryPRGSeedCountLifetime.generateWithTrace fresh
        parsed.1.2.logical.request state
      let before := BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
        frame parsed hParsed rich generated.1.1
      let after := BinaryTerminalPhysicalAllowanceSeed.run frame parsed hParsed rich generated.1.1
      have hs := BinaryTerminalPhysicalAllowanceSeed.run_trace_delta
        frame parsed hParsed rich generated.1.1
      have hc : BinaryPRGHeapPrimitiveLifetime.cells after.1.2 ≤
          BinaryPRGHeapPrimitiveLifetime.cells before.2+
            (32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich)) := by
        simpa only [before,after,Nat.add_assoc] using hs.1
      have hf : framePeak after.1.2 ≤
          framePeak before.2+(framePeak (calculatorTrace parsed.1 rich)+28) := by
        simpa only [before,after,Nat.add_assoc] using hs.2
      have hw := wrap_third_delta 48 2 decoded.2 generated.2 before.2 after.1.2
        (32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich))
        (framePeak (calculatorTrace parsed.1 rich)+28) hc hf
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 48 2 [decoded.2,generated.2,after.1.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 48 2 [decoded.2,generated.2,before.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
        framePeak (wrap 48 2 [decoded.2,generated.2,after.1.2]) ≤
          framePeak (wrap 48 2 [decoded.2,generated.2,before.2])+
            framePeak (calculatorTrace parsed.1 rich)+30
      exact ⟨hw.1.trans_eq (by omega),hw.2.trans_eq (by omega)⟩
    · rename_i hTail
      rw [reference_tail fresh rich frame state parsed hParsed hTail]
      change BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [decoded.2]) ≤
          BinaryPRGHeapPrimitiveLifetime.cells (wrap 32 2 [decoded.2])+
            32+BinaryPRGHeapPrimitiveLifetime.cells (calculatorTrace parsed.1 rich) ∧
        framePeak (wrap 32 2 [decoded.2]) ≤
          framePeak (wrap 32 2 [decoded.2])+framePeak (calculatorTrace parsed.1 rich)+30
      exact ⟨by omega,by omega⟩

theorem run_usage {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    usage (run fresh rich frame state).1.2 ≤
      usage (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh rich frame state).2+
        usage (rawCalculatorTrace rich frame)+62 := by
  have h := run_trace_delta fresh rich frame state
  unfold usage
  omega

theorem uniform_carried_work : ∃ C d : ℕ, ∀ {S : Type*}
    (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    (run fresh rich frame state).2+
      BinaryBigEndian.littleValue (run fresh rich frame state).1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceSeed.accepted_uniform_carried_work
  refine ⟨C,d,?_⟩
  intro S fresh rich frame state
  unfold run
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hParsed
    split
    · exact hBound frame parsed hParsed rich _
    · exact Nat.zero_le _

theorem uniform_usage : ∃ C d : ℕ, ∀ {S : Type*}
    (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    usage (run fresh rich frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalFreshRawLifetime.uniform_usage
  obtain ⟨P,e,hCalc⟩ := BinaryTerminalPhysicalAllowanceRaw.rawCalculatorTrace_polynomial
  refine ⟨C+P*3^e+62,max d e,?_⟩
  intro S fresh rich frame state
  exact polynomial_with_frame_overhead _ _ _ _ 62 C P d e
    (hOld fresh rich frame state) (hCalc rich frame) (run_usage fresh rich frame state)

theorem uniform_all_prefix : ∃ C d : ℕ, ∀ {S : Type*}
    (fresh : S → Bool × S) (rich : Bool) (frame : List Bool)
    (state : S) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length) (run fresh rich frame state).1.2 steps ≤
        borrowed+frame.length+B ∧
      framePeak ((run fresh rich frame state).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := uniform_usage
  exact ⟨C,d,fun fresh rich frame state borrowed steps =>
    all_prefix _ _ (hBound fresh rich frame state) (borrowed+frame.length) steps⟩

def pair {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S) :
    ((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ :=
  let rich := run fresh true frame state
  let poor := run fresh false frame rich.1.1.1.2
  let data := ((rich.1.1.1.1,poor.1.1.1.1),poor.1.1.1.2)
  (((data,(rich.1.1.2,poor.1.1.2)),wrap 64 2 [rich.1.2,poor.1.2]),rich.2+poor.2)

theorem pair_data {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S) :
    (pair fresh frame state).1.1.1 =
      (BinaryPRGBooleanFreshPairLifetime.runWithTrace fresh frame state).1 := by
  simp only [pair,BinaryPRGBooleanFreshPairLifetime.runWithTrace,run_data]

theorem pair_counted {S : Type*} (fresh : S → Bool × S)
    (frame : List Bool) (state : S) (calls : ℕ) :
    (pair (FreshBitSeedLifetime.countedFresh fresh) frame (state,calls)).1.1.1 =
      ((pair fresh frame state).1.1.1.1,((pair fresh frame state).1.1.1.2,
        calls+2*BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [pair_data,BinaryPRGBooleanFreshPairLifetime.runWithTrace_counted]

theorem pair_vector (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+
      sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    (pair (FreshBitSeedLifetime.tapeFresh (FreshBitSeedLifetime.vectorTape bits)) frame 0).1.1.1 =
      ((some (prepared.2.request.output true (firstBitBlock _ _ bits)),
        some (prepared.2.request.output false (secondBitBlock _ _ bits))),
        sampleBitBudget prepared.1 prepared.2.request.precision+
          sampleBitBudget prepared.1 prepared.2.request.precision) := by
  rw [pair_data]
  exact BinaryPRGBooleanFreshPairLifetime.runWithTrace_vector frame prepared hRead bits

theorem pair_uniform_carried_work : ∃ C d : ℕ, ∀ {S : Type*}
    (fresh : S → Bool × S) (frame : List Bool) (state : S),
    (pair fresh frame state).2+
      BinaryBigEndian.littleValue (pair fresh frame state).1.1.2.1+
      BinaryBigEndian.littleValue (pair fresh frame state).1.1.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_carried_work
  refine ⟨2*C,d,?_⟩
  intro S fresh frame state
  have hr := hBound fresh true frame state
  have hp := hBound fresh false frame (run fresh true frame state).1.1.1.2
  unfold pair
  dsimp only
  nlinarith only [hr,hp]

theorem pair_uniform_usage : ∃ C d : ℕ, ∀ {S : Type*}
    (fresh : S → Bool × S) (frame : List Bool) (state : S),
    usage (pair fresh frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_usage
  refine ⟨2*C+128,d,?_⟩
  intro S fresh frame state
  have hr := hBound fresh true frame state
  have hp := hBound fresh false frame (run fresh true frame state).1.1.1.2
  have hw := wrap_usage 64 2 [(run fresh true frame state).1.2,
    (run fresh false frame (run fresh true frame state).1.1.1.2).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  have hOne := Nat.one_le_pow d (frame.length+1) (by omega)
  change usage (wrap 64 2 [_,_]) ≤ _
  nlinarith only [hr,hp,hw,hOne]

theorem pair_uniform_all_prefix : ∃ C d : ℕ, ∀ {S : Type*}
    (fresh : S → Bool × S) (frame : List Bool) (state : S) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length) (pair fresh frame state).1.2 steps ≤
        borrowed+frame.length+B ∧
      framePeak ((pair fresh frame state).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := pair_uniform_usage
  exact ⟨C,d,fun fresh frame state borrowed steps =>
    all_prefix _ _ (hBound fresh frame state) (borrowed+frame.length) steps⟩

end Blotto.BinaryTerminalPhysicalAllowanceFresh
