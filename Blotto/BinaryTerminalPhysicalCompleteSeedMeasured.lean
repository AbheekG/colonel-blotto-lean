import Blotto.BinarySamplerExecutionCharges
import Blotto.BinarySeedPreparationEmission
import Blotto.BinarySeedWrapperEmission
import Blotto.BinaryTerminalPhysicalCompleteFramedMeasured
import Blotto.BinaryTerminalPhysicalOutputSeed

/-! The actual measured seed validator/store builder feeds the complete
measured terminal/global-fallback/output path once. Rejection never draws.
Previous bytes and encoded allowance survive; the source charge now includes
validation, store preparation, all terminal regimes, fallback and output. -/
namespace Blotto.BinaryTerminalPhysicalCompleteSeedMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open RationalLottoResourceSystem
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Held {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) :=
  BinaryPRGTapeSeedBlocks.Blocks n prepared.request.precision × (BinarySeedLookupTree.Store × Trace)

theorem prepared_some {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool)
    (held : Held prepared) (h : (BinarySeedPreparationMeasured.prepare prepared seed).1.1 = some held) :
    ∃ blocks : BinaryPRGTapeSeedBlocks.Blocks n prepared.request.precision,
      held = (blocks,BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits) := by
  have he := congrArg Prod.fst (BinarySeedPreparationMeasured.prepare_erases prepared seed)
  have hm : (BinaryPRGBooleanSeedBlocks.readWithTrace prepared seed).1.map
      (fun tapes => (tapes,BinaryWordStoreLifetime.prepareWithTrace tapes.choice.bits)) = some held := he.symm.trans h
  cases hb : (BinaryPRGBooleanSeedBlocks.readWithTrace prepared seed).1 with
  | none => simp only [hb,Option.map_none] at hm; cases hm
  | some blocks =>
      rw [hb,Option.map_some] at hm
      exact ⟨blocks,(Option.some.inj hm).symm⟩

theorem prepared_trace {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) :
    (BinarySeedPreparationMeasured.prepare prepared seed).1.2 = (BinaryPRGBooleanSeedBlocks.readWithTrace prepared seed).2 :=
  congrArg Prod.snd (BinarySeedPreparationMeasured.prepare_erases prepared seed)

def runReference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let prepared := BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed
  match prepared.1.1 with
  | none => (((none,[]),wrap 16 2 [prepared.1.2]),prepared.2+4)
  | some held =>
      let drawn := BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed held.2.1 rich
        parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header
      (((some drawn.1.1.1.1,drawn.1.1.2),
        wrap 32 2 [prepared.1.2,wrap 16 2 [held.2.2,drawn.1.2]]),prepared.2+drawn.2+8)


def runWithCharges (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges :=
  let returned := BinarySeedPreparationEmission.prepare parsed.1.2.logical seed
  let prepared := returned.1
  match prepared.1.1 with
  | none =>
      let emitted := BinaryWrapperEmission.one 16 2 prepared.1.2
      ((((none,[]),emitted.1),prepared.2+4),
        BinarySamplerExecutionCharges.addWrapper
          (BinarySamplerExecutionCharges.ofExecution BinarySamplerExecutionCharges.zero.execution returned.2) emitted.2)
  | some held =>
      let returnedDraw := BinaryTerminalPhysicalCompleteFramedMeasured.runWithCharges frame parsed hParsed held.2.1 rich
        parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header
      let drawn := returnedDraw.1
      let emitted := BinarySeedWrapperEmission.nested prepared.1.2 held.2.2 drawn.1.2
      ((((some drawn.1.1.1.1,drawn.1.1.2),emitted.1),prepared.2+drawn.2+8),
        BinarySamplerExecutionCharges.addWrapper (BinarySamplerExecutionCharges.ofExecution returnedDraw.2 returned.2) emitted.2)

def run (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  (runWithCharges frame parsed hParsed rich seed).1

theorem run_eq_reference (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : run frame parsed hParsed rich seed = runReference frame parsed hParsed rich seed := by
  unfold run runWithCharges runReference
  simp only [BinarySeedPreparationEmission.prepare_compat,BinaryTerminalPhysicalCompleteFramedMeasured.run]
  split <;> simp only [BinaryWrapperEmission.one_trace,BinarySeedWrapperEmission.nested_trace]

theorem runWithCharges_compat (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : (runWithCharges frame parsed hParsed rich seed).1 = run frame parsed hParsed rich seed := rfl

theorem runWithCharges_seedEmission (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (runWithCharges frame parsed hParsed rich seed).2.seedEmission =
      (BinarySeedPreparationEmission.prepare parsed.1.2.logical seed).2 := by
  unfold runWithCharges
  dsimp only
  split <;> rfl

theorem run_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1 = (BinaryTerminalPhysicalOutputSeed.run frame parsed hParsed rich seed).1.1 := by
  rw [run_eq_reference]
  unfold runReference BinaryTerminalPhysicalOutputSeed.run
  dsimp only
  cases h : (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.1 with
  | none => rfl
  | some held =>
      exact congrArg (fun data => (some data.1.1,data.2))
        (BinaryTerminalPhysicalCompleteFramedMeasured.run_data frame parsed hParsed held.2.1 rich
          parsed.1.2.logical.request.precision held.1.outer held.1.scalar parsed.1.2.logical.header)

theorem accepted_request (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (run frame parsed hParsed rich seed).1.1.1 =
      (RationalPRGBinaryRequest.seedTable (sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision) seed).map
        (fun table => parsed.1.2.logical.request.output rich table.read) := by
  rw [run_data]
  exact BinaryTerminalPhysicalOutputSeed.accepted_request frame parsed hParsed rich seed

theorem frame_parameters (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    parsed.1.2.logical.request.precision ≤ frame.length+5 ∧ parsed.1.2.logical.header.bytes.length ≤ 2*frame.length+3 := by
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hAcc : (BinaryPRGAccuracyRulerRequest.read frame).1 = some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hAcc
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hH := BinaryPRGSeedOutputLifetimePolynomial.header_length parsed.1.2.logical.header
  exact ⟨hK,by omega⟩

theorem store_parameters (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1 parsed.1.2.logical.request.precision) :
    let store := (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1
    frame.length+parsed.1.2.logical.request.precision+store.width+store.cap.value+parsed.1.2.logical.header.bytes.length+3 ≤
      20000*(frame.length+1) := by
  have hStore := BinaryTerminalPhysicalAllowanceSeed.accepted_store_size frame parsed hParsed blocks
  have hFields := frame_parameters frame parsed hParsed
  dsimp only at hStore ⊢
  omega

theorem preparation_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (seed : List Bool) :
    usage (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).1.2 ≤ 10000000*(frame.length+1)^2 := by
  rw [prepared_trace,BinaryPRGBooleanSeedBlocks.read_same]
  exact (BinaryPRGTapeSeedBlocks.read_usage parsed.1.1 parsed.1.2.logical.request.precision seed).trans
    (BinaryTerminalPhysicalSeedOutputLifetime.accepted_preparation_polynomial frame parsed hParsed)

theorem store_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1 parsed.1.2.logical.request.precision) :
    usage (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).2 ≤ 500000*(frame.length+1) := by
  let store := BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits
  let N := blocks.choice.bits.length
  have hStore := BinaryWordStoreLifetime.prepareWithTrace_bounds blocks.choice.bits
  change listCells store.2+arraySlots store.2 ≤ 46*N+20 ∧ framePeak store.2 ≤ 2*N+binaryWordWidth N+12 at hStore
  have hLog : binaryWordWidth N ≤ N+1 := BinaryPRGSeedOutputLifetimePolynomial.wordWidth_le N
  have hSize := BinaryTerminalPhysicalAllowanceSeed.accepted_store_size frame parsed hParsed blocks
  have hCap : store.1.cap.value = N := by
    rw [BinaryWordStoreLifetime.prepareWithTrace_erases,BinarySeedLookupTree.prepare_cap]
  change frame.length+store.1.width+store.1.cap.value+3 ≤ 10000*(frame.length+1) at hSize
  change usage store.2 ≤ _
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

end Blotto.BinaryTerminalPhysicalCompleteSeedMeasured
