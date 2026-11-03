import Blotto.BinarySeedPreparationMeasured
import Blotto.BinaryTerminalPhysicalAllowanceSeed

/-! The measured validator/store result feeds physical allowance framing
directly. The returned natural charge now includes seed validation and store
preparation as well as cache-prefix work. Seed generation and terminal runtime
are separate components; native observer evaluation is not priced here. -/

namespace Blotto.BinaryTerminalPhysicalPreparationWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage RationalLottoResourceSystem
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let prepared := BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed
  match prepared.1.1 with
  | none => (((none,[]),wrap 16 2 [prepared.1.2]),prepared.2)
  | some held =>
      let drawn := BinaryTerminalPhysicalAllowanceFramed.run frame parsed hParsed
        held.2.1 rich parsed.1.2.logical.request.precision
        held.1.outer held.1.scalar parsed.1.2.logical.header
      (((some drawn.1.1.1.1,drawn.1.1.2),
        wrap 32 2 [prepared.1.2,wrap 16 2 [held.2.2,drawn.1.2]]),drawn.2+prepared.2)

theorem run_erases (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1 =
      (BinaryTerminalPhysicalAllowanceSeed.run frame parsed hParsed rich seed).1 := by
  unfold run BinaryTerminalPhysicalAllowanceSeed.run BinaryTerminalPhysicalAllowanceSeed.output
  dsimp only
  rw [BinarySeedPreparationMeasured.prepare_erases]
  cases h : (BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed).1 <;> rfl

theorem run_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).2 =
      (BinaryTerminalPhysicalAllowanceSeed.run frame parsed hParsed rich seed).2+
        (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).2 := by
  unfold run BinaryTerminalPhysicalAllowanceSeed.run BinaryTerminalPhysicalAllowanceSeed.output
  dsimp only
  rw [BinarySeedPreparationMeasured.prepare_erases]
  cases h : (BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed).1 with
  | none => simp only [Option.map_none,Nat.zero_add]
  | some tapes => rfl

theorem run_total_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 =
      (BinaryTerminalPhysicalAllowanceSeed.run frame parsed hParsed rich seed).2+
        BinaryBigEndian.littleValue
          (BinaryTerminalPhysicalAllowanceSeed.run frame parsed hParsed rich seed).1.1.2+
        (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).2 := by
  rw [run_work,run_erases]
  omega

theorem run_prefix_preparation_charge (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).2+
      BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 =
      (((BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed).1.map
        (fun tapes => BinaryTerminalPhysicalAllowanceSeed.prefixWork parsed.1
          (BinaryWordStoreLifetime.prepareWithTrace tapes.choice.bits).1 rich+
          BinaryTerminalPhysicalAllowanceSeed.calculatorWork parsed.1 rich)).getD 0)+
        (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).2 := by
  rw [run_total_work,BinaryTerminalPhysicalAllowanceSeed.run_carried_total_work]

theorem preparation_frame_bound (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : List Bool) :
    (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).2 ≤
      128000*(frame.length+1) := by
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hAcc : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hSeed := BinaryPRGSeedRequestBound.read_seedCount_bound
    frame (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hAcc
  change sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision ≤
    BinaryPRGSeedRequestBound.seedCountBound frame.length at hSeed
  unfold BinaryPRGSeedRequestBound.seedCountBound at hSeed
  have hPrep := BinarySeedPreparationMeasured.prepare_bound parsed.1.2.logical seed
  omega

theorem accepted_uniform_work : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool),
      (run frame parsed hParsed rich seed).2+
        BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 ≤
        C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceSeed.accepted_uniform_carried_work
  refine ⟨C+128000,d+1,?_⟩
  intro frame parsed hParsed rich seed
  have ho := hBound frame parsed hParsed rich seed
  have hp := preparation_frame_bound frame parsed hParsed seed
  have he := run_total_work frame parsed hParsed rich seed
  have hX : 0 < frame.length+1 := by omega
  have hUp := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right hX (show d ≤ d+1 by omega))
  have hLinear : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ d+1 by omega)
  have hScale := Nat.mul_le_mul_left 128000 hLinear
  nlinarith only [ho,hp,he,hUp,hScale]

theorem accepted_request (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1.1 =
      (RationalPRGBinaryRequest.seedTable
        (sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision) seed).map
        (fun table => parsed.1.2.logical.request.output rich table.read) := by
  rw [run_erases]
  exact BinaryTerminalPhysicalAllowanceSeed.accepted_request frame parsed hParsed rich seed

theorem accepted_uniform_usage : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : Parsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool),
      usage (run frame parsed hParsed rich seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceSeed.accepted_uniform_usage
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich seed
  rw [run_erases]
  exact hBound frame parsed hParsed rich seed

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

end Blotto.BinaryTerminalPhysicalPreparationWork
