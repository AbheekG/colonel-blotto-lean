import Blotto.BinaryTerminalPhysicalEmissionFramed
import Blotto.BinaryTerminalPhysicalOutputSeed

/-! Actual measured seed validation/store preparation feeds measured terminal
emission and physical output. Word bytes, Boolean allowance and the whole output
law are unchanged. The source charge still omits group factory/draw, native row
projection, complete parsing and native observer/reference/allocator prices. -/

namespace Blotto.BinaryTerminalPhysicalEmissionSeed
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open RationalLottoResourceSystem BinaryCachedGroupInputHeight BinaryMeasuredEmissionGrowth
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let prepared := BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed
  match prepared.1.1 with
  | none => (((none,[]),wrap 16 2 [prepared.1.2]),prepared.2)
  | some held =>
      let drawn := BinaryTerminalPhysicalEmissionFramed.run frame parsed hParsed held.2.1 rich
        parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header
      (((some drawn.1.1.1.1,drawn.1.1.2),
        wrap 32 2 [prepared.1.2,wrap 16 2 [held.2.2,drawn.1.2]]),drawn.2+prepared.2)

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1 =
      (BinaryTerminalPhysicalOutputSeed.run frame parsed hParsed rich seed).1.1 := by
  unfold run BinaryTerminalPhysicalOutputSeed.run
  dsimp only
  cases h : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 with
  | none => rfl
  | some held => simp only [BinaryTerminalPhysicalEmissionFramed.run_data]

def delta (n : ℕ) : ℕ := BinaryTerminalPhysicalEmissionFramed.delta n+4

theorem run_growth (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    Growth (BinaryTerminalPhysicalOutputSeed.run frame parsed hParsed rich seed).1.2
      (run frame parsed hParsed rich seed).1.2 (delta parsed.1.1) := by
  unfold run BinaryTerminalPhysicalOutputSeed.run
  dsimp only
  cases h : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 with
  | none => exact ⟨Nat.le_add_right _ _,Nat.le_add_right _ _⟩
  | some held =>
      have hDraw := BinaryTerminalPhysicalEmissionFramed.run_growth frame parsed hParsed held.2.1 rich
        parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header
      have hInner := wrap_pair 16 2 held.2.2 _ _ _ hDraw
      exact wrap_pair 32 2 (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.2 _ _ _ hInner

theorem run_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).2 ≤
      (BinaryTerminalPhysicalOutputSeed.run frame parsed hParsed rich seed).2+
        BinaryWordTerminalEmissionMeasured.workEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request)
          parsed.1.2.logical.request.precision+68*(parsed.1.1+1)^2+16 := by
  unfold run BinaryTerminalPhysicalOutputSeed.run
  dsimp only
  cases h : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 with
  | none => simp only; omega
  | some held =>
      have hd := BinaryTerminalPhysicalEmissionFramed.run_work frame parsed hParsed held.2.1 rich
        parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header
      change _+_ ≤ _+_+_+_+16
      omega

theorem accepted_extra_work : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed),
    BinaryWordTerminalEmissionMeasured.workEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request)
      parsed.1.2.logical.request.precision+68*(parsed.1.1+1)^2+16 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalEmissionFixed.accepted_extra_work
  refine ⟨C*8^d,d,?_⟩
  intro frame parsed hParsed
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hAcc : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hAcc
  change parsed.1.2.logical.request.precision ≤ frame.length+5 at hK
  have hSize : frame.length+parsed.1.2.logical.request.precision+3 ≤ 8*(frame.length+1) := by omega
  have hPower := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
  rw [Nat.mul_pow] at hPower
  exact (hBound frame parsed hParsed parsed.1.2.logical.request.precision).trans
    (hPower.trans_eq (by ring))

theorem accepted_uniform_work : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool),
    (run frame parsed hParsed rich seed).2+BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 ≤
      C*(frame.length+1)^d := by
  obtain ⟨C₁,d₁,hOld⟩ := BinaryTerminalPhysicalOutputSeed.accepted_uniform_work
  obtain ⟨C₂,d₂,hExtra⟩ := accepted_extra_work
  refine ⟨C₁+C₂,max d₁ d₂,?_⟩
  intro frame parsed hParsed rich seed
  have ho := hOld frame parsed hParsed rich seed
  have he := hExtra frame parsed hParsed
  have hw := run_work frame parsed hParsed rich seed
  have hX : 0 < frame.length+1 := by omega
  have h₁ := Nat.mul_le_mul_left C₁ (Nat.pow_le_pow_right hX (Nat.le_max_left d₁ d₂))
  have h₂ := Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_right hX (Nat.le_max_right d₁ d₂))
  rw [run_data]
  nlinarith only [ho,he,hw,h₁,h₂]

theorem accepted_request (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1.1 =
      (RationalPRGBinaryRequest.seedTable (sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision) seed).map
        (fun table => parsed.1.2.logical.request.output rich table.read) := by
  rw [run_data]
  exact BinaryTerminalPhysicalOutputSeed.accepted_request frame parsed hParsed rich seed

theorem delta_polynomial (n : ℕ) : delta n ≤ 4102*(n+4)^2 := by
  have h := BinaryTerminalPhysicalEmissionFramed.delta_polynomial n
  have hPositive : 1 ≤ (n+4)^2 := by
    have h : 0 < (n+4)^2 := by positivity
    omega
  unfold delta
  nlinarith only [h,hPositive]

theorem accepted_uniform_usage : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool), usage (run frame parsed hParsed rich seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalOutputSeed.accepted_uniform_usage
  refine ⟨C+131264,max d 2,?_⟩
  intro frame parsed hParsed rich seed
  have ho := hOld frame parsed hParsed rich seed
  have hg := usage_growth _ _ _ (run_growth frame parsed hParsed rich seed)
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hd := delta_polynomial parsed.1.1
  have hX : 0 < frame.length+1 := by omega
  have h₁ := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d 2))
  have h₂ : (parsed.1.1+4)^2 ≤ 16*(frame.length+1)^(max d 2) := by
    calc
      _ ≤ (4*(frame.length+1))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = 16*(frame.length+1)^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (Nat.le_max_right _ _))
  nlinarith only [ho,hg,hd,h₁,h₂]

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

end Blotto.BinaryTerminalPhysicalEmissionSeed
