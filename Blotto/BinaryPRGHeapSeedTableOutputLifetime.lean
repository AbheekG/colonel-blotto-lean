import Blotto.BinaryPRGPhysicalFramedLifetime
import Blotto.BinaryPRGWordControllerFramed
import Blotto.BinaryWordStoreLifetime

/-! The prepared choice array feeds its actual list copy and traced Boolean
seed store. Retained scalar/outer cursor views feed the complete physical draw/global fallback and
heap/slot-array scaling/direct-tape-framing path. The original prepared request and arrays remain borrowed. -/
namespace Blotto.BinaryPRGHeapSeedTableOutputLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option maxHeartbeats 2000000

def outputWithTrace {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) : List Bool × Trace :=
  let seed := tables.choice.data.toList
  let store := BinaryWordStoreLifetime.prepareWithTrace seed
  let output := BinaryPRGPhysicalFramedLifetime.runWithTrace store.1 prepared.request rich prepared.request.precision
    tables.outerView tables.scalarView prepared.header
  (output.1.1,wrapList tables.choice.data.size 16 (tables.choice.data.size+2) [store.2,output.2])

theorem outputWithTrace_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputWithTrace prepared rich tables).1 = BinaryPRGWordControllerFramed.output prepared rich tables := by
  unfold outputWithTrace
  dsimp only
  rw [BinaryPRGPhysicalFramedLifetime.run_bytes,BinaryWordStoreLifetime.prepareWithTrace_erases]
  simp only [BinaryPRGSeedBlocks.Tables.outerView_read,BinaryPRGSeedBlocks.Tables.scalarView_read]
  unfold BinaryPRGWordControllerFramed.output BinaryStoredRowFrame.row
  rw [← prepared.header.correct,← BinaryPRGSeedBlocks.listOfFn_read tables.choice]
  rfl

theorem outputWithTrace_original {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputWithTrace prepared rich tables).1 = (BinaryPRGSeedBlockOutput.output prepared rich tables).1 := by
  rw [outputWithTrace_state]
  exact BinaryPRGWordControllerFramed.output_state prepared rich tables

theorem outputWithTrace_request {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputWithTrace prepared rich tables).1 = prepared.request.output rich tables.flat := by
  rw [outputWithTrace_original,BinaryPRGSeedBlockOutput.output_state,BinaryPRGAccuracyRulerRequest.output_state,
    BinaryPRGOutputRun.output_state,BinaryPRGCachedRequest.output_state]

theorem outputWithTrace_read {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) (suffix : List Bool) :
    BinaryRatListFrame.readRow ((outputWithTrace prepared rich tables).1++suffix) =
      some (n,List.ofFn (if rich then prepared.request.source.richSample prepared.request.precision tables.flat
        else prepared.request.source.poorSample prepared.request.precision tables.flat),suffix) := by
  rw [outputWithTrace_request]
  exact prepared.request.output_read rich tables.flat suffix

theorem outputWithTrace_budget {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    RationalPRGBinaryRequest.ReturnedBudget n (if rich then prepared.request.source.a else prepared.request.source.b)
      (outputWithTrace prepared rich tables).1 := by
  rw [outputWithTrace_request]
  exact prepared.request.output_returned_budget rich tables.flat

theorem store_dimensions {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (BinarySeedLookupTree.prepare tables.choice.data.toList).cap.value = coinBitBudget n prepared.request.precision ∧
      (BinarySeedLookupTree.prepare tables.choice.data.toList).width ≤ binaryWordWidth (coinBitBudget n prepared.request.precision) := by
  have hCap := BinarySeedLookupTree.prepare_cap tables.choice.data.toList
  have hWidth := BinarySeedLookupTree.prepare_width_bound tables.choice.data.toList
  simp only [Array.length_toList,tables.choice.size] at hCap hWidth
  exact ⟨hCap,hWidth⟩

noncomputable def envelope {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) : ℕ :=
  let store := BinarySeedLookupTree.prepare tables.choice.data.toList
  let N := coinBitBudget n prepared.request.precision
  BinaryPRGPhysicalFramedLifetime.envelope prepared.request prepared.request.precision store.width store.cap.value
    prepared.header.bytes.length+50*N+binaryWordWidth N+64

theorem outputWithTrace_usage {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    usage (outputWithTrace prepared rich tables).2 ≤ envelope prepared tables := by
  let seed := tables.choice.data.toList
  let store := BinaryWordStoreLifetime.prepareWithTrace seed
  let output := BinaryPRGPhysicalFramedLifetime.runWithTrace store.1 prepared.request rich prepared.request.precision
    tables.outerView tables.scalarView prepared.header
  have hE : store.1 = BinarySeedLookupTree.prepare seed := BinaryWordStoreLifetime.prepareWithTrace_erases seed
  have hStore := BinaryWordStoreLifetime.prepareWithTrace_bounds seed
  have hUsage : usage store.2 ≤ 48*seed.length+binaryWordWidth seed.length+32 := by
    change listCells store.2+arraySlots store.2 ≤ 46*seed.length+20 ∧
      framePeak store.2 ≤ 2*seed.length+binaryWordWidth seed.length+12 at hStore
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hOutput := BinaryPRGPhysicalFramedLifetime.run_usage store.1 prepared.request rich prepared.request.precision
    tables.outerView tables.scalarView prepared.header
  change usage output.2 ≤ _ at hOutput
  have hOutput' := hOutput.trans_eq (congrArg (fun seedStore : BinarySeedLookupTree.Store =>
    BinaryPRGPhysicalFramedLifetime.envelope prepared.request prepared.request.precision seedStore.width seedStore.cap.value
      prepared.header.bytes.length) hE)
  have hLength : seed.length = coinBitBudget n prepared.request.precision := by
    dsimp only [seed]
    rw [Array.length_toList,tables.choice.size]
  rw [hLength] at hUsage
  have hw := wrapList_usage tables.choice.data.size 16 (tables.choice.data.size+2) [store.2,output.2]
  change usage (outputWithTrace prepared rich tables).2 ≤ _ at hw
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,tables.choice.size] at hw
  change usage (outputWithTrace prepared rich tables).2 ≤
    BinaryPRGPhysicalFramedLifetime.envelope prepared.request prepared.request.precision
      (BinarySeedLookupTree.prepare seed).width (BinarySeedLookupTree.prepare seed).cap.value prepared.header.bytes.length+
      50*coinBitBudget n prepared.request.precision+binaryWordWidth (coinBitBudget n prepared.request.precision)+64
  omega

theorem all_prefix {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) (borrowed steps : ℕ) :
    retainedHeap borrowed (outputWithTrace prepared rich tables).2 steps ≤ borrowed+envelope prepared tables ∧
      framePeak ((outputWithTrace prepared rich tables).2.take steps) ≤ envelope prepared tables :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (outputWithTrace_usage prepared rich tables) borrowed steps

end Blotto.BinaryPRGHeapSeedTableOutputLifetime
