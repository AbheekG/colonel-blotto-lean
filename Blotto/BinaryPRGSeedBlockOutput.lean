import Blotto.BinaryPRGSeedBlockInterface

/-! The output runner consumes the three prepared seed arrays directly.
Its fixed native draw, selected fallback, original scaling and retained-header
framing exactly equal the original flat-vector output and full output ledger.
Top-level flat block offset additions are absent from this entry point;
remaining in-block/index/controller/physical costs are separate. -/

namespace Blotto.BinaryPRGSeedBlockOutput
open BinaryRationalNormalization BinaryPRGOutputPrimitiveWork RationalLottoResourceSystem

def output {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) : List Bool × BinaryPRGOutputRun.Ledger :=
  let normalized := BinaryPRGOutputRun.fixedSample prepared.request rich prepared.request.precision
    (coinBitBudget n prepared.request.precision) tables.outer.read tables.scalar.read tables.choice.read
  let scaled := rescaleWithWork prepared.request.prepared.original.a normalized.1
  let frame := prepared.header.bytes ++ BinaryStoredRowFrame.words (List.ofFn scaled.1.read)
  let visits := BinaryStoredRowFrameWork.wordsVisits (List.ofFn scaled.1.read) + 2 * n + prepared.header.bytes.length
  (frame,{normalized.2 with scaling := scaled.2,coordinateFraming := visits})

theorem output_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    output prepared rich tables = BinaryPRGAccuracyRulerRequest.output prepared rich tables.flat := by
  unfold output BinaryPRGAccuracyRulerRequest.output BinaryPRGOutputRun.originalSample BinaryPRGOutputRun.sample BinaryPRGOutputRun.innerSample
  rw [tables.outer_eq,tables.scalar_eq,tables.choice_eq]

theorem output_map_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) (seed : List Bool) :
    (BinaryPRGSeedBlocks.read n prepared.request.precision seed).1.map (output prepared rich) =
      (RationalPRGBinaryRequest.seedTable (sampleBitBudget n prepared.request.precision) seed).map
        (fun table => BinaryPRGAccuracyRulerRequest.output prepared rich table.read) := by
  have hFunction : output prepared rich =
      (fun tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision =>
        BinaryPRGAccuracyRulerRequest.output prepared rich tables.flat) :=
    funext (fun tables => output_state prepared rich tables)
  rw [hFunction]
  have hb := BinaryPRGSeedBlocks.read_flat_state n prepared.request.precision seed
  have hm := congrArg (fun readers : Option (Fin (sampleBitBudget n prepared.request.precision) → Bool) =>
    readers.map (BinaryPRGAccuracyRulerRequest.output (n := n) prepared rich)) hb
  simpa only [Option.map_map,Function.comp_def] using hm

end Blotto.BinaryPRGSeedBlockOutput
