import Blotto.BinaryTerminalPhysicalEmissionFixed
import Blotto.BinaryTerminalPhysicalOutputFramed

/-! Physical output consumes the row returned by measured terminal emission.
The source charge joins cached prefix, emission, exhaustion fallback and
physical output. Group factory/draw, row projection, complete parsing and native
observer/reference/ownership/allocator prices remain separate. The enlarged
trace has a quadratic additive reservation bound, rather than old-trace equality. -/

namespace Blotto.BinaryTerminalPhysicalEmissionFramed
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryMeasuredEmissionGrowth BinaryCachedGroupInputHeight
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ :=
  let drawn := BinaryTerminalPhysicalEmissionFixed.fixed frame parsed hParsed seed rich K outer scalar
  let output := BinaryPhysicalOutputMeasured.output
    parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  ((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),
    wrapList parsed.1.1 32 (parsed.1.1+2) [drawn.1.2,output.1.2]),drawn.2+output.2)

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).1.1 =
      (BinaryTerminalPhysicalOutputFramed.run frame parsed hParsed seed rich K outer scalar header).1.1 := by
  simp only [run,BinaryTerminalPhysicalOutputFramed.run,BinaryTerminalPhysicalEmissionFixed.fixed_data]

def delta (n : ℕ) : ℕ := BinaryTerminalPhysicalEmissionFixed.fixedDelta n+2

set_option backward.isDefEq.respectTransparency true in
theorem run_growth (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    Growth (BinaryTerminalPhysicalOutputFramed.run frame parsed hParsed seed rich K outer scalar header).1.2
      (run frame parsed hParsed seed rich K outer scalar header).1.2 (delta parsed.1.1) := by
  let before := BinaryTerminalPhysicalAllowanceFramed.fixed frame parsed hParsed seed rich K outer scalar
  let after := BinaryTerminalPhysicalEmissionFixed.fixed frame parsed hParsed seed rich K outer scalar
  let output := BinaryPhysicalOutputMeasured.output
    parsed.1.2.logical.request.prepared.original.a header.bytes before.1.1.1.1.data.toList
  have h := BinaryTerminalPhysicalEmissionFixed.fixed_growth frame parsed hParsed seed rich K outer scalar
  have hw := BinaryPhysicalHeapAllowanceRequest.wrapList_head_delta parsed.1.1 32 (parsed.1.1+2)
    before.1.2 after.1.2 [output.1.2] (BinaryTerminalPhysicalEmissionFixed.fixedDelta parsed.1.1)
    (BinaryTerminalPhysicalEmissionFixed.fixedDelta parsed.1.1) h.1 h.2
  unfold run BinaryTerminalPhysicalOutputFramed.run
  dsimp only
  simp only [BinaryTerminalPhysicalEmissionFixed.fixed_data]
  with_reducible
    change Growth (wrapList parsed.1.1 32 (parsed.1.1+2) [before.1.2,output.1.2])
      (wrapList parsed.1.1 32 (parsed.1.1+2) [after.1.2,output.1.2]) (delta parsed.1.1)
  unfold Growth
  with_reducible exact ⟨hw.1.trans (by unfold delta; omega),hw.2.trans_eq (by unfold delta; omega)⟩

theorem run_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).2 ≤
      (BinaryTerminalPhysicalOutputFramed.run frame parsed hParsed seed rich K outer scalar header).2+
        BinaryWordTerminalEmissionMeasured.workEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request) K+
          68*(parsed.1.1+1)^2+16 := by
  have h := BinaryTerminalPhysicalEmissionFixed.fixed_work frame parsed hParsed seed rich K outer scalar
  simp only [run,BinaryTerminalPhysicalOutputFramed.run,BinaryTerminalPhysicalEmissionFixed.fixed_data]
  omega

theorem delta_polynomial (n : ℕ) : delta n ≤ 4098*(n+4)^2 := by
  have h := BinaryTerminalPhysicalEmissionFixed.fixedDelta_polynomial n
  have hPositive : 1 ≤ (n+4)^2 := by
    have h : 0 < (n+4)^2 := by positivity
    omega
  unfold delta
  nlinarith only [h,hPositive]

theorem run_usage_growth (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
      usage (BinaryTerminalPhysicalOutputFramed.run frame parsed hParsed seed rich K outer scalar header).1.2+
        2*delta parsed.1.1 :=
  usage_growth _ _ _ (run_growth frame parsed hParsed seed rich K outer scalar header)

theorem accepted_uniform_work : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1),
    (run frame parsed hParsed seed rich K outer scalar header).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar header).1.1.2 ≤
      C*(frame.length+seed.width+seed.cap.value+K+header.bytes.length+3)^d := by
  obtain ⟨C₁,d₁,hOld⟩ := BinaryTerminalPhysicalOutputFramed.accepted_uniform_work
  obtain ⟨C₂,d₂,hExtra⟩ := BinaryTerminalPhysicalEmissionFixed.accepted_extra_work
  refine ⟨C₁+C₂,max d₁ d₂,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  let X := frame.length+seed.width+seed.cap.value+K+header.bytes.length+3
  have hX : 0 < X := by dsimp only [X]; omega
  have ho := hOld frame parsed hParsed seed rich K outer scalar header
  have he := hExtra frame parsed hParsed K
  have hw := run_work frame parsed hParsed seed rich K outer scalar header
  have h₁ : C₁*X^d₁ ≤ C₁*X^(max d₁ d₂) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (Nat.le_max_left _ _))
  have h₂ : C₂*(frame.length+K+3)^d₂ ≤ C₂*X^(max d₁ d₂) := by
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by dsimp only [X]; omega) d₂).trans
      (Nat.pow_le_pow_right hX (Nat.le_max_right _ _))
  rw [run_data]
  change _ ≤ (C₁+C₂)*X^(max d₁ d₂)
  change _ ≤ C₁*X^d₁ at ho
  nlinarith only [ho,he,hw,h₁,h₂]

theorem accepted_uniform_usage : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1),
    usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
      C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+4)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalOutputFramed.accepted_uniform_usage
  refine ⟨C+8196,max d 2,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  let X := frame.length+K+seed.width+seed.cap.value+header.bytes.length+4
  have hX : 0 < X := by dsimp only [X]; omega
  have ho := hOld frame parsed hParsed seed rich K outer scalar header
  have hg := run_usage_growth frame parsed hParsed seed rich K outer scalar header
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hd := delta_polynomial parsed.1.1
  have h₁ : C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d ≤ C*X^(max d 2) := by
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by dsimp only [X]; omega) d).trans
      (Nat.pow_le_pow_right hX (Nat.le_max_left _ _))
  have h₂ : (parsed.1.1+4)^2 ≤ X^(max d 2) :=
    (Nat.pow_le_pow_left (by dsimp only [X]; omega) 2).trans
      (Nat.pow_le_pow_right hX (Nat.le_max_right _ _))
  change _ ≤ (C+8196)*X^(max d 2)
  nlinarith only [ho,hg,hd,h₁,h₂]

theorem all_prefix : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) (borrowed steps : ℕ),
    retainedHeap borrowed (run frame parsed hParsed seed rich K outer scalar header).1.2 steps ≤
      borrowed+C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+4)^d ∧
    framePeak ((run frame parsed hParsed seed rich K outer scalar header).1.2.take steps) ≤
      C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+4)^d := by
  obtain ⟨C,d,hBound⟩ := accepted_uniform_usage
  exact ⟨C,d,fun frame parsed hParsed seed rich K outer scalar header borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _
      (hBound frame parsed hParsed seed rich K outer scalar header) borrowed steps⟩

end Blotto.BinaryTerminalPhysicalEmissionFramed
