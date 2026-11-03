import Blotto.BinaryTerminalPhysicalFullRawLifetime
import Blotto.BinaryPRGBooleanFreshRawLifetime

/-! The fresh-bit complete raw runner retains the physical parser's stores
through seed generation and terminal output. Its fresh state, bytes and
source-trace usage are compared with the established Boolean-counter runner. -/
namespace Blotto.BinaryTerminalPhysicalFreshRawLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option maxHeartbeats 3000000

def runWithTrace {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (Option (List Bool) × S) × Trace :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => ((none,state),wrap 24 2 [decoded.2])
  | some parsed =>
      if parsed.2 = [] then
        let seed := BinaryPRGSeedCountLifetime.generateWithTrace fresh
          parsed.1.2.logical.request state
        let output := BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
          frame parsed hParsed rich seed.1.1
        ((output.1,seed.1.2),wrap 48 2 [decoded.2,seed.2,output.2])
      else ((none,state),wrap 32 2 [decoded.2])

private theorem trace_none {S : Type*} (fresh : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    (runWithTrace fresh rich frame state).2 =
      wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2] := by
  unfold runWithTrace
  dsimp only
  split
  · rfl
  · rename_i parsed hSome
    rw [hRead] at hSome
    cases hSome

private theorem trace_accept {S : Type*} (fresh : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    (runWithTrace fresh rich frame state).2 =
      wrap 48 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
        (BinaryPRGSeedCountLifetime.generateWithTrace fresh
          parsed.1.2.logical.request state).2,
        (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
          frame parsed hRead rich
            (BinaryPRGSeedCountLifetime.generateWithTrace fresh
              parsed.1.2.logical.request state).1.1).2] := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i parsed' hSome
    rw [hRead] at hSome
    obtain rfl := Option.some.inj hSome
    simp only [ite_eq_left hTail]

private theorem trace_tail {S : Type*} (fresh : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    (runWithTrace fresh rich frame state).2 =
      wrap 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2] := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i parsed' hSome
    rw [hRead] at hSome
    obtain rfl := Option.some.inj hSome
    simp only [ite_eq_right hTail]

private theorem full_trace_none (rich : Bool) (frame seed : List Bool)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).2 =
      wrap 16 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2] := by
  unfold BinaryTerminalPhysicalFullRawLifetime.runWithTrace
  dsimp only
  split
  · rfl
  · rename_i parsed hSome
    rw [hRead] at hSome
    cases hSome

private theorem full_trace_accept (rich : Bool) (frame seed : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).2 =
      wrap 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
        (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
          frame parsed hRead rich seed).2] := by
  unfold BinaryTerminalPhysicalFullRawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i parsed' hSome
    rw [hRead] at hSome
    obtain rfl := Option.some.inj hSome
    simp only [ite_eq_left hTail]

private theorem full_trace_tail (rich : Bool) (frame seed : List Bool)
    (parsed : (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).2 =
      wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2] := by
  unfold BinaryTerminalPhysicalFullRawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i parsed' hSome
    rw [hRead] at hSome
    obtain rfl := Option.some.inj hSome
    simp only [ite_eq_right hTail]

theorem runWithTrace_state {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (runWithTrace fresh rich frame state).1 =
      (BinaryPRGBooleanFreshRawLifetime.runWithTrace fresh rich frame state).1 := by
  have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hNone,Option.map_none] at hRef
    simp only [BinaryPRGBooleanFreshRawLifetime.runWithTrace,← hRef]
  · rename_i parsed hSome
    rw [hSome,Option.map_some] at hRef
    split
    · rename_i hTail
      simp only [BinaryPRGBooleanFreshRawLifetime.runWithTrace,← hRef,
        BinaryPRGPhysicalRawRequestLifetime.forgetParsed,ite_eq_left hTail]
      rw [BinaryTerminalPhysicalSeedOutputLifetime.accepted_state,
        BinaryPRGSeedCountLifetime.generate_state]
    · rename_i hTail
      simp only [BinaryPRGBooleanFreshRawLifetime.runWithTrace,← hRef,
        BinaryPRGPhysicalRawRequestLifetime.forgetParsed,ite_eq_right hTail]

theorem runWithTrace_counted {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (calls : ℕ) :
    (runWithTrace (FreshBitSeedLifetime.countedFresh fresh) rich frame
      (state,calls)).1 =
      ((runWithTrace fresh rich frame state).1.1,
        ((runWithTrace fresh rich frame state).1.2,
          calls+BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [runWithTrace_state,
    BinaryPRGBooleanFreshRawLifetime.runWithTrace_counted]

theorem accepted_returns {S : Type*} (fresh : S → Bool × S)
    (rich : Bool) (frame : List Bool)
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 =
      some (parsed,[])) (state : S) :
    ∃ bits : Fin (sampleBitBudget parsed.1
      parsed.2.logical.request.precision) → Bool,
      (runWithTrace fresh rich frame state).1.1 =
        some (parsed.2.logical.request.output rich bits) := by
  have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  rw [hRead,Option.map_some] at hRef
  have hOld : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 =
      some ((⟨parsed.1,parsed.2.logical⟩ :
        Σ n,BinaryPRGAccuracyRulerRequest.Request n),[]) := by
    simpa only [BinaryPRGPhysicalRawRequestLifetime.forgetParsed] using hRef.symm
  rw [runWithTrace_state]
  exact BinaryPRGBooleanFreshRawLifetime.accepted_returns
    fresh rich frame ⟨parsed.1,parsed.2.logical⟩ hOld state

theorem returned_budget {S : Type*} (fresh : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S)
    (bytes : List Bool)
    (h : (runWithTrace fresh rich frame state).1.1 = some bytes) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1,parsed.2.source⟩ :
          Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) bytes := by
  rw [runWithTrace_state,
    BinaryPRGBooleanFreshRawLifetime.runWithTrace_state] at h
  exact BinaryPRGFreshRawLifetime.runWithTrace_returned_budget
    fresh rich frame state bytes h

theorem usage_comparison {S : Type*} (fresh : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    ∃ seed : List Bool,
      usage (runWithTrace fresh rich frame state).2 ≤
        usage (BinaryTerminalPhysicalFullRawLifetime.runWithTrace
          rich frame seed).2+2000000*(frame.length+400)^2+64 := by
  have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  cases hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 with
  | none =>
      refine ⟨[],?_⟩
      have h := BinaryPRGFreshRawLifetime.reject_usage 16
        (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2
      norm_num only at h
      rw [trace_none fresh rich frame state hRead,
        full_trace_none rich frame [] hRead]
      omega
  | some parsed =>
      rw [hRead,Option.map_some] at hRef
      have hOld : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 =
          some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := hRef.symm
      by_cases hTail : parsed.2 = []
      · let seed := BinaryPRGSeedCountLifetime.generateWithTrace fresh
          parsed.1.2.logical.request state
        refine ⟨seed.1.1,?_⟩
        have hGen := BinaryPRGSeedCountLifetime.raw_usage fresh frame
          (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed)
          hOld state
        have hInsert := BinaryPRGFreshRawLifetime.insert_usage
          (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2
          seed.2
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
            frame parsed hRead rich seed.1.1).2
        change usage seed.2 ≤ _ at hGen
        rw [trace_accept fresh rich frame state parsed hRead hTail,
          full_trace_accept rich frame seed.1.1 parsed hRead hTail]
        change usage (wrap 48 2
          [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
            seed.2,
            (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
              frame parsed hRead rich seed.1.1).2]) ≤
          usage (wrap 32 2
            [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
              (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
                frame parsed hRead rich seed.1.1).2])+
            2000000*(frame.length+400)^2+64
        omega
      · refine ⟨[],?_⟩
        have h := BinaryPRGFreshRawLifetime.reject_usage 24
          (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2
        norm_num only at h
        rw [trace_tail fresh rich frame state parsed hRead hTail,
          full_trace_tail rich frame [] parsed hRead hTail]
        omega

theorem uniform_usage : ∃ C d : ℕ, ∀ {S : Type*}
    (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    usage (runWithTrace fresh rich frame state).2 ≤
      C*(frame.length+1)^d := by
  rcases BinaryTerminalPhysicalFullRawLifetime.uniform_usage with
    ⟨C,d,hBound⟩
  let A := 2000000*400^2
  refine ⟨C+A+64,d+2,?_⟩
  intro S fresh rich frame state
  obtain ⟨seed,hCompare⟩ := usage_comparison fresh rich frame state
  have hOld := hBound rich frame seed
  have hX : 0 < frame.length+1 := by omega
  have hUp := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right hX (show d ≤ d+2 by omega))
  have hSquare := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right hX (show 2 ≤ d+2 by omega))
  have hOne := Nat.one_le_pow (d+2) (frame.length+1) hX
  have hScale := Nat.mul_le_mul_left 2000000
    (Nat.pow_le_pow_left
      (show frame.length+400 ≤ 400*(frame.length+1) by omega) 2)
  rw [Nat.mul_pow] at hScale
  dsimp only [A] at *
  nlinarith

theorem uniform_all_prefix : ∃ C d : ℕ, ∀ {S : Type*}
    (fresh : S → Bool × S) (rich : Bool) (frame : List Bool)
    (state : S) (borrowed steps : ℕ),
    retainedHeap (borrowed+frame.length)
        (runWithTrace fresh rich frame state).2 steps ≤
        borrowed+frame.length+C*(frame.length+1)^d ∧
      framePeak ((runWithTrace fresh rich frame state).2.take steps) ≤
        C*(frame.length+1)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun fresh rich frame state borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _
      (hBound fresh rich frame state) _ steps⟩

end Blotto.BinaryTerminalPhysicalFreshRawLifetime
