import Blotto.BinaryTerminalPhysicalOutputFramed
import Blotto.BinaryTerminalPhysicalPreparationWork

/-! Measured validation/store preparation feeds the selected measured-output
framer once. The charge covers validation, choice-store construction, cache
prefix and physical output from the returned decoded row. Terminal/fallback,
row projection, parser and native observer/reference/allocator prices are open. -/

namespace Blotto.BinaryTerminalPhysicalOutputSeed
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open RationalLottoResourceSystem
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem framed_output_polynomial : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (outer scalar : BinaryScalarTape parsed.1.2.logical.request.precision),
    BinaryTerminalPhysicalOutputFramed.outputCharge frame parsed hParsed seed rich
      parsed.1.2.logical.request.precision outer scalar parsed.1.2.logical.header ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOutput⟩ := BinaryTerminalPhysicalOutputFramed.output_polynomial
  refine ⟨C*16^d,d,?_⟩
  intro frame parsed hParsed seed rich outer scalar
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hAcc : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hAcc
  change parsed.1.2.logical.request.precision ≤ frame.length+5 at hK
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hh := BinaryPRGSeedOutputLifetimePolynomial.header_length parsed.1.2.logical.header
  have hSize : frame.length+parsed.1.2.logical.request.precision+
      parsed.1.2.logical.header.bytes.length+3 ≤ 16*(frame.length+1) := by omega
  have hPower := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hPower
  exact (hOutput frame parsed hParsed seed rich parsed.1.2.logical.request.precision
    outer scalar parsed.1.2.logical.header).trans (hPower.trans_eq (by ring))

/-- Ghost observer on the actual validated choice store; not called by `run`. -/
def outputCharge (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ℕ :=
  ((BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1.map (fun held =>
    BinaryTerminalPhysicalOutputFramed.outputCharge frame parsed hParsed held.2.1 rich
      parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header)).getD 0

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let prepared := BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed
  match prepared.1.1 with
  | none => (((none,[]),wrap 16 2 [prepared.1.2]),prepared.2)
  | some held =>
      let drawn := BinaryTerminalPhysicalOutputFramed.run frame parsed hParsed held.2.1 rich
        parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header
      (((some drawn.1.1.1.1,drawn.1.1.2),
        wrap 32 2 [prepared.1.2,wrap 16 2 [held.2.2,drawn.1.2]]),drawn.2+prepared.2)

theorem run_erases (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1 =
      (BinaryTerminalPhysicalPreparationWork.run frame parsed hParsed rich seed).1 := by
  unfold run BinaryTerminalPhysicalPreparationWork.run
  dsimp only
  cases h : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 with
  | none => simp only
  | some held => simp only [BinaryTerminalPhysicalOutputFramed.run_erases]

theorem run_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).2 =
      (BinaryTerminalPhysicalPreparationWork.run frame parsed hParsed rich seed).2+
        outputCharge frame parsed hParsed rich seed := by
  unfold run BinaryTerminalPhysicalPreparationWork.run outputCharge
  dsimp only
  cases h : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 with
  | none => simp only [Option.map_none,Option.getD_none,Nat.add_zero]
  | some held => simp only [Option.map_some,Option.getD_some,BinaryTerminalPhysicalOutputFramed.run_work]; omega

theorem run_total_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).2+BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 =
      (BinaryTerminalPhysicalPreparationWork.run frame parsed hParsed rich seed).2+
        BinaryBigEndian.littleValue (BinaryTerminalPhysicalPreparationWork.run frame parsed hParsed rich seed).1.1.2+
          outputCharge frame parsed hParsed rich seed := by
  rw [run_work,run_erases]
  omega

theorem output_polynomial : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool), outputCharge frame parsed hParsed rich seed ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOutput⟩ := framed_output_polynomial
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich seed
  unfold outputCharge
  cases h : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 with
  | none => simp only [Option.map_none,Option.getD_none]; exact Nat.zero_le _
  | some held => exact hOutput frame parsed hParsed held.2.1 rich held.1.outer held.1.scalar

theorem accepted_uniform_work : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool),
    (run frame parsed hParsed rich seed).2+BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 ≤
      C*(frame.length+1)^d := by
  obtain ⟨C₁,d₁,hOld⟩ := BinaryTerminalPhysicalPreparationWork.accepted_uniform_work
  obtain ⟨C₂,d₂,hOutput⟩ := output_polynomial
  refine ⟨C₁+C₂,max d₁ d₂,?_⟩
  intro frame parsed hParsed rich seed
  have ho := hOld frame parsed hParsed rich seed
  have hp := hOutput frame parsed hParsed rich seed
  have hX : 0 < frame.length+1 := by omega
  have h₁ := Nat.mul_le_mul_left C₁ (Nat.pow_le_pow_right hX (Nat.le_max_left d₁ d₂))
  have h₂ := Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_right hX (Nat.le_max_right d₁ d₂))
  rw [run_total_work]
  nlinarith only [ho,hp,h₁,h₂]

theorem accepted_request (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1.1 =
      (RationalPRGBinaryRequest.seedTable (sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision) seed).map
        (fun table => parsed.1.2.logical.request.output rich table.read) := by
  rw [run_erases]
  exact BinaryTerminalPhysicalPreparationWork.accepted_request frame parsed hParsed rich seed

theorem accepted_uniform_usage : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool), usage (run frame parsed hParsed rich seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalPreparationWork.accepted_uniform_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich seed
  rw [run_erases]
  exact hBound frame parsed hParsed rich seed

theorem accepted_all_prefix : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length+seed.length) (run frame parsed hParsed rich seed).1.2 steps ≤
        borrowed+frame.length+seed.length+B ∧
      framePeak ((run frame parsed hParsed rich seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := accepted_uniform_usage
  exact ⟨C,d,fun frame parsed hParsed rich seed borrowed steps =>
    all_prefix _ _ (hBound frame parsed hParsed rich seed) (borrowed+frame.length+seed.length) steps⟩

end Blotto.BinaryTerminalPhysicalOutputSeed
