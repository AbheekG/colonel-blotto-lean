import Blotto.BinaryPhysicalOutputMeasured
import Blotto.BinaryTerminalPhysicalAllowanceFramed

/-! The selected Boolean-allowance terminal feeds its returned row directly to
the measured physical output. The charge includes cache-prefix and output
work; terminal drawing/fallback, row projection, complete parser and native
observer/reference/allocator prices remain separate. -/

namespace Blotto.BinaryTerminalPhysicalOutputFramed
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryPRGHeapFixedProperties
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Erased specification observer; `run` consumes its returned row once. -/
def outputCharge (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) : ℕ :=
  let drawn := BinaryTerminalPhysicalAllowanceFramed.fixed frame parsed hParsed seed rich K outer scalar
  (BinaryPhysicalOutputMeasured.output parsed.1.2.logical.request.prepared.original.a
    header.bytes drawn.1.1.1.1.data.toList).2

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    ((((List Bool × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ) :=
  let drawn := BinaryTerminalPhysicalAllowanceFramed.fixed frame parsed hParsed seed rich K outer scalar
  let output := BinaryPhysicalOutputMeasured.output
    parsed.1.2.logical.request.prepared.original.a header.bytes drawn.1.1.1.1.data.toList
  ((((output.1.1,drawn.1.1.1.2),drawn.1.1.2),
    wrapList parsed.1.1 32 (parsed.1.1+2) [drawn.1.2,output.1.2]),drawn.2+output.2)

theorem run_erases (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).1 =
      (BinaryTerminalPhysicalAllowanceFramed.run frame parsed hParsed seed rich K outer scalar header).1 := by
  simp only [run,BinaryTerminalPhysicalAllowanceFramed.run,BinaryPhysicalOutputMeasured.output_erases]

theorem run_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (run frame parsed hParsed seed rich K outer scalar header).2 =
      (BinaryTerminalPhysicalAllowanceFramed.run frame parsed hParsed seed rich K outer scalar header).2+
        outputCharge frame parsed hParsed seed rich K outer scalar header := rfl

theorem output_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    outputCharge frame parsed hParsed seed rich K outer scalar header ≤
      BinaryPhysicalOutputLifetime.bound parsed.1.1
        (wordWidth parsed.1.2.logical.request K) header.bytes.length := by
  have hRow := (congrArg Prod.fst
    (BinaryTerminalPhysicalAllowanceFramed.fixed_data frame parsed hParsed seed rich K outer scalar)).trans
    (congrArg Prod.fst
      (BinaryTerminalPhysicalFixedLifetime.accepted_logical_output frame parsed hParsed seed rich K outer scalar))
  unfold outputCharge
  dsimp only
  rw [hRow]
  exact BinaryPhysicalOutputMeasured.actual_output_work seed parsed.1.2.logical.request rich K outer scalar header.bytes

theorem output_polynomial : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1),
    outputCharge frame parsed hParsed seed rich K outer scalar header ≤
      C*(frame.length+K+header.bytes.length+3)^d := by
  obtain ⟨C,d,hExtra⟩ := BinaryPRGPhysicalOutputPolynomial.extra_polynomial
  refine ⟨C*5^d,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  let request := parsed.1.2.logical.request
  let s := request.source.originalInputWordWidth
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hExtraBound := hExtra ⟨parsed.1.1,s,K,0,0,header.bytes.length⟩
  change BinaryPRGPhysicalOutputPolynomial.extraEnvelope parsed.1.1 s K header.bytes.length ≤
    C*(parsed.1.1+s+K+0+0+header.bytes.length+1)^d at hExtraBound
  have hBase : BinaryPhysicalOutputLifetime.bound parsed.1.1 (wordWidth request K) header.bytes.length ≤
      BinaryPRGPhysicalOutputPolynomial.extraEnvelope parsed.1.1 s K header.bytes.length := by
    change BinaryPhysicalOutputLifetime.bound parsed.1.1
      (1+2*expressionHeightBudget (max (3+s) (K+2)) 75) header.bytes.length ≤ _
    dsimp only [BinaryPRGPhysicalOutputPolynomial.extraEnvelope,BinaryPRGPhysicalOutputPolynomial.extraEnvelopeAt]
    omega
  have hSize : parsed.1.1+s+K+0+0+header.bytes.length+1 ≤
      5*(frame.length+K+header.bytes.length+3) := by
    dsimp only [s,request] at *
    omega
  have hPower := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hPower
  exact (output_bound frame parsed hParsed seed rich K outer scalar header).trans
    ((hBase.trans hExtraBound).trans (hPower.trans_eq (by ring)))

theorem accepted_uniform_work : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1),
    (run frame parsed hParsed seed rich K outer scalar header).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed seed rich K outer scalar header).1.1.2 ≤
      C*(frame.length+seed.width+seed.cap.value+K+header.bytes.length+3)^d := by
  obtain ⟨C₁,d₁,hOld⟩ := BinaryTerminalPhysicalAllowanceFramed.accepted_uniform_carried_work
  obtain ⟨C₂,d₂,hOutput⟩ := output_polynomial
  refine ⟨C₁+C₂,max d₁ d₂,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  let X := frame.length+seed.width+seed.cap.value+K+header.bytes.length+3
  have hX : 0 < X := by dsimp only [X]; omega
  have ho := hOld frame parsed hParsed seed rich K outer scalar header
  have hp := hOutput frame parsed hParsed seed rich K outer scalar header
  have h₁ : C₁*(frame.length+seed.width+seed.cap.value+3)^d₁ ≤ C₁*X^(max d₁ d₂) := by
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by dsimp only [X]; omega) d₁).trans
      (Nat.pow_le_pow_right hX (Nat.le_max_left _ _))
  have h₂ : C₂*(frame.length+K+header.bytes.length+3)^d₂ ≤ C₂*X^(max d₁ d₂) := by
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by dsimp only [X]; omega) d₂).trans
      (Nat.pow_le_pow_right hX (Nat.le_max_right _ _))
  rw [run_work,run_erases]
  change _ ≤ (C₁+C₂)*X^(max d₁ d₂)
  nlinarith only [ho,hp,h₁,h₂]

theorem accepted_uniform_usage : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1),
    usage (run frame parsed hParsed seed rich K outer scalar header).1.2 ≤
      C*(frame.length+K+seed.width+seed.cap.value+header.bytes.length+3)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceFramed.accepted_uniform_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich K outer scalar header
  rw [run_erases]
  exact hBound frame parsed hParsed seed rich K outer scalar header

end Blotto.BinaryTerminalPhysicalOutputFramed
