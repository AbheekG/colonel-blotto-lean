import Blotto.BinaryPRGBooleanSeedBlocks
import Blotto.BinaryPRGTapeSeedOutputLifetime
import Blotto.BinaryPRGHeapSeedTableOutputLifetime

/-! Operational seed validation/preparation feeds its actual returned tapes
into the complete physical output path. Truncated and surplus seeds execute
only preparation; output factories are not called on rejection. The prepared
request/header remain borrowed at this interface. -/
namespace Blotto.BinaryPRGHeapSeedOutputLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option maxHeartbeats 2000000

def runWithTrace {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) : Option (List Bool) × Trace :=
  let blocks := BinaryPRGBooleanSeedBlocks.readWithTrace prepared seed
  match blocks.1 with
  | none => (none,wrap 16 2 [blocks.2])
  | some tapes =>
      let output := BinaryPRGTapeSeedOutputLifetime.outputWithTrace prepared rich tapes
      (some output.1,wrap 32 2 [blocks.2,output.2])

theorem runWithTrace_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) :
    (runWithTrace prepared rich seed).1 = (BinaryPRGSeedBlocks.read n prepared.request.precision seed).1.map
      (fun tables => (BinaryPRGSeedBlockOutput.output prepared rich tables).1) := by
  rw [← BinaryPRGTapeSeedBlocks.read_state]
  unfold runWithTrace
  rw [BinaryPRGBooleanSeedBlocks.read_same]
  dsimp only
  cases h : (BinaryPRGTapeSeedBlocks.readWithTrace n prepared.request.precision seed).1 with
  | none => simp only [h,Option.map_none]
  | some tapes => simp only [h,Option.map_some,BinaryPRGTapeSeedOutputLifetime.output_original]

theorem runWithTrace_request {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) :
    (runWithTrace prepared rich seed).1 =
      (RationalPRGBinaryRequest.seedTable (sampleBitBudget n prepared.request.precision) seed).map
        (fun table => prepared.request.output rich table.read) := by
  rw [runWithTrace_state]
  have h := congrArg (fun result : Option (List Bool × BinaryPRGOutputRun.Ledger) => result.map Prod.fst)
    (BinaryPRGSeedBlockOutput.output_map_state prepared rich seed)
  simpa only [Option.map_map,Function.comp_def,BinaryPRGAccuracyRulerRequest.output_state,
    BinaryPRGOutputRun.output_state,BinaryPRGCachedRequest.output_state] using h

theorem runWithTrace_reject {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) :
    (runWithTrace prepared rich seed).1 = none ↔ (BinaryPRGSeedBlocks.read n prepared.request.precision seed).1 = none := by
  rw [runWithTrace_state,Option.map_eq_none_iff]

theorem runWithTrace_read {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed bytes : List Bool) (h : (runWithTrace prepared rich seed).1 = some bytes) :
    ∃ tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision,
      (BinaryPRGSeedBlocks.read n prepared.request.precision seed).1 = some tables ∧
      tables.flatList = seed ∧ ∀ suffix,
        BinaryRatListFrame.readRow (bytes++suffix) =
          some (n,List.ofFn (if rich then prepared.request.source.richSample prepared.request.precision tables.flat
            else prepared.request.source.poorSample prepared.request.precision tables.flat),suffix) := by
  rw [runWithTrace_state] at h
  obtain ⟨tables,hTables,hBytes⟩ := Option.map_eq_some_iff.mp h
  refine ⟨tables,hTables,BinaryPRGSeedBlocks.read_success_flatList _ _ _ _ hTables,?_⟩
  intro suffix
  rw [← hBytes,← BinaryPRGHeapSeedTableOutputLifetime.outputWithTrace_original]
  exact BinaryPRGHeapSeedTableOutputLifetime.outputWithTrace_read prepared rich tables suffix

theorem runWithTrace_budget {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed bytes : List Bool) (h : (runWithTrace prepared rich seed).1 = some bytes) :
    RationalPRGBinaryRequest.ReturnedBudget n (if rich then prepared.request.source.a else prepared.request.source.b) bytes := by
  rw [runWithTrace_state] at h
  obtain ⟨tables,hTables,hBytes⟩ := Option.map_eq_some_iff.mp h
  rw [← hBytes,← BinaryPRGHeapSeedTableOutputLifetime.outputWithTrace_original]
  exact BinaryPRGHeapSeedTableOutputLifetime.outputWithTrace_budget prepared rich tables

def preparationEnvelope (n K : ℕ) : ℕ :=
  ownedBound (sampleBitBudget n K)+2*sampleBitBudget n K+10

theorem preparation_usage (n K : ℕ) (seed : List Bool) :
    usage (BinarySeedPreparationSpace.readWithTrace n K seed).2 ≤ preparationEnvelope n K := by
  rw [readWithTrace_trace]
  have h := readTrace_bounds n K seed
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells preparationEnvelope ownedBound
  omega

noncomputable def envelope {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool) : ℕ :=
  preparationEnvelope n prepared.request.precision +
    ((BinaryPRGSeedBlocks.read n prepared.request.precision seed).1.map
      (BinaryPRGHeapSeedTableOutputLifetime.envelope prepared)).getD 0 + 128

theorem runWithTrace_usage {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) : usage (runWithTrace prepared rich seed).2 ≤ envelope prepared seed := by
  let blocks := BinaryPRGTapeSeedBlocks.readWithTrace n prepared.request.precision seed
  have hPrep := BinaryPRGTapeSeedBlocks.read_usage n prepared.request.precision seed
  change usage blocks.2 ≤ preparationEnvelope n prepared.request.precision at hPrep
  have hState : blocks.1.map BinaryPRGTapeSeedBlocks.Blocks.erase =
      (BinaryPRGSeedBlocks.read n prepared.request.precision seed).1 := BinaryPRGTapeSeedBlocks.read_state _ _ _
  unfold runWithTrace
  rw [BinaryPRGBooleanSeedBlocks.read_same]
  dsimp only
  split
  · rename_i hNone
    have hw := wrap_usage 16 2 [blocks.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [blocks.2]) ≤ _
    unfold envelope
    rw [← hState,hNone]
    simp only [Option.map_none,Option.getD_none]
    omega
  · rename_i tapes hSome
    have hOut := BinaryPRGTapeSeedOutputLifetime.output_usage prepared rich tapes
    have hw := wrap_usage 32 2 [blocks.2,(BinaryPRGTapeSeedOutputLifetime.outputWithTrace prepared rich tapes).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [blocks.2,(BinaryPRGTapeSeedOutputLifetime.outputWithTrace prepared rich tapes).2]) ≤ _
    unfold envelope
    rw [← hState,hSome]
    simp only [Option.map_some,Option.getD_some]
    omega

theorem reject_usage {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) (h : (runWithTrace prepared rich seed).1 = none) :
    usage (runWithTrace prepared rich seed).2 ≤ 5*sampleBitBudget n prepared.request.precision+32 := by
  have hReject := (runWithTrace_reject prepared rich seed).mp h
  have hArrays := BinaryPRGTapeSeedBlocks.reject_arrays n prepared.request.precision seed hReject
  have hBounds := BinaryPRGTapeSeedBlocks.trace_bounds n prepared.request.precision seed
  have hPrep : usage (BinaryPRGTapeSeedBlocks.readWithTrace n prepared.request.precision seed).2 ≤
      5*sampleBitBudget n prepared.request.precision+10 := by
    rw [BinaryPRGTapeSeedBlocks.read_trace] at hArrays ⊢
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  unfold runWithTrace
  rw [BinaryPRGBooleanSeedBlocks.read_same]
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryPRGTapeSeedBlocks.readWithTrace n prepared.request.precision seed).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryPRGTapeSeedBlocks.readWithTrace n prepared.request.precision seed).2]) ≤ _
    omega
  · rename_i tapes hSome
    have hState := BinaryPRGTapeSeedBlocks.read_state n prepared.request.precision seed
    rw [hSome,hReject] at hState
    cases hState

theorem all_prefix {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+seed.length) (runWithTrace prepared rich seed).2 steps ≤
      borrowed+seed.length+envelope prepared seed ∧
    framePeak ((runWithTrace prepared rich seed).2.take steps) ≤ envelope prepared seed :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage prepared rich seed) _ steps

theorem reject_all_prefix {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) (borrowed steps : ℕ) (h : (runWithTrace prepared rich seed).1 = none) :
    retainedHeap (borrowed+seed.length) (runWithTrace prepared rich seed).2 steps ≤
      borrowed+seed.length+(5*sampleBitBudget n prepared.request.precision+32) ∧
    framePeak ((runWithTrace prepared rich seed).2.take steps) ≤ 5*sampleBitBudget n prepared.request.precision+32 :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (reject_usage prepared rich seed h) _ steps

end Blotto.BinaryPRGHeapSeedOutputLifetime
