import Blotto.BinaryPRGTapeSeedBlocks
import Blotto.BinaryPRGHeapSeedTableOutputLifetime

/-! Actual validated tapes feed one physical choice store and both scalar
views. Native table erasure is used only for exact semantics/source envelopes;
no seed-array packing, array projection or compatibility closure is executed. -/
namespace Blotto.BinaryPRGTapeSeedOutputLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
open BinaryPRGTapeSeedBlocks
set_option maxHeartbeats 2000000

def outputWithTrace {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (blocks : Blocks n prepared.request.precision) : List Bool × Trace :=
  let store := BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits
  let output := BinaryPRGPhysicalFramedLifetime.runWithTrace store.1 prepared.request rich prepared.request.precision
    blocks.outer blocks.scalar prepared.header
  (output.1.1,wrap 16 2 [store.2,output.2])

theorem output_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (blocks : Blocks n prepared.request.precision) :
    (outputWithTrace prepared rich blocks).1 =
      (BinaryPRGHeapSeedTableOutputLifetime.outputWithTrace prepared rich blocks.erase).1 := by
  simp only [outputWithTrace,BinaryPRGHeapSeedTableOutputLifetime.outputWithTrace,
    Blocks.erase_choice,Blocks.erase_outer,Blocks.erase_scalar]
  rw [Blocks.erase_choice]

theorem output_original {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (blocks : Blocks n prepared.request.precision) :
    (outputWithTrace prepared rich blocks).1 = (BinaryPRGSeedBlockOutput.output prepared rich blocks.erase).1 := by
  rw [output_state,BinaryPRGHeapSeedTableOutputLifetime.outputWithTrace_original]

theorem output_usage {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (blocks : Blocks n prepared.request.precision) :
    usage (outputWithTrace prepared rich blocks).2 ≤ BinaryPRGHeapSeedTableOutputLifetime.envelope prepared blocks.erase := by
  let seed := blocks.choice.bits
  let store := BinaryWordStoreLifetime.prepareWithTrace seed
  let output := BinaryPRGPhysicalFramedLifetime.runWithTrace store.1 prepared.request rich prepared.request.precision
    blocks.outer blocks.scalar prepared.header
  have hE : store.1 = BinarySeedLookupTree.prepare seed := BinaryWordStoreLifetime.prepareWithTrace_erases seed
  have hStore := BinaryWordStoreLifetime.prepareWithTrace_bounds seed
  have hUsage : usage store.2 ≤ 48*seed.length+binaryWordWidth seed.length+32 := by
    change listCells store.2+arraySlots store.2 ≤ 46*seed.length+20 ∧
      framePeak store.2 ≤ 2*seed.length+binaryWordWidth seed.length+12 at hStore
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hOutput := BinaryPRGPhysicalFramedLifetime.run_usage store.1 prepared.request rich prepared.request.precision
    blocks.outer blocks.scalar prepared.header
  change usage output.2 ≤ _ at hOutput
  have hOutput' := hOutput.trans_eq (congrArg (fun seedStore : BinarySeedLookupTree.Store =>
    BinaryPRGPhysicalFramedLifetime.envelope prepared.request prepared.request.precision seedStore.width seedStore.cap.value
      prepared.header.bytes.length) hE)
  have hLength : seed.length = coinBitBudget n prepared.request.precision := blocks.choice.size
  rw [hLength] at hUsage
  have hw := wrap_usage 16 2 [store.2,output.2]
  change usage (outputWithTrace prepared rich blocks).2 ≤ _ at hw
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  unfold BinaryPRGHeapSeedTableOutputLifetime.envelope
  rw [Blocks.erase_choice]
  change usage (outputWithTrace prepared rich blocks).2 ≤
    BinaryPRGPhysicalFramedLifetime.envelope prepared.request prepared.request.precision
      (BinarySeedLookupTree.prepare seed).width (BinarySeedLookupTree.prepare seed).cap.value prepared.header.bytes.length+
      50*coinBitBudget n prepared.request.precision+binaryWordWidth (coinBitBudget n prepared.request.precision)+64
  omega

end Blotto.BinaryPRGTapeSeedOutputLifetime
