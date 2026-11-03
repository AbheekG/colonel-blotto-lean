import Blotto.BinaryPRGWordControllerRequest
import Blotto.BinaryPRGSeedPreparedRun

/-! The raw framing interface now consumes the concrete Store/Boolean-counter
draw and quadratic data-only output scaling. Original parsing, precision and
seed validation are retained. Every output byte and rejection matches the old
request. This is exact execution refinement; the complete input/controller/
backend/address/lifetime price is not inferred from byte equality. -/

namespace Blotto.BinaryPRGWordControllerFramed
open BinaryRationalNormalization BinaryRationalEncoding RationalLottoResourceSystem

def output {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) : List Bool :=
  let normalized := BinaryPRGWordControllerRequest.vectorFixedSample prepared.request rich
    prepared.request.precision (coinBitBudget n prepared.request.precision)
    tables.outer.read tables.scalar.read tables.choice.read
  let scaled := FixedArrayTable.ofFn (fun j => BinaryQuadraticData.apply .mul
    prepared.request.prepared.original.a (normalized.read j))
  prepared.header.bytes ++ BinaryStoredRowFrame.words (List.ofFn scaled.read)

theorem output_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    output prepared rich tables = (BinaryPRGSeedBlockOutput.output prepared rich tables).1 := by
  have hNormalized := BinaryPRGWordControllerRequest.vectorFixedSample_state prepared.request rich
    prepared.request.precision (coinBitBudget n prepared.request.precision)
    tables.outer.read tables.scalar.read tables.choice.read
  have hOld := (BinaryPRGOutputRun.fixedSample_state prepared.request rich prepared.request.precision
    (coinBitBudget n prepared.request.precision) tables.outer.read tables.scalar.read tables.choice.read).trans
    (BinaryPRGEmissionRun.fixedSample_state prepared.request rich prepared.request.precision
      (coinBitBudget n prepared.request.precision) tables.outer.read tables.scalar.read tables.choice.read)
  have hScale : (FixedArrayTable.ofFn (fun j => BinaryQuadraticData.apply .mul
      prepared.request.prepared.original.a
      ((BinaryPRGWordControllerRequest.vectorFixedSample prepared.request rich prepared.request.precision
        (coinBitBudget n prepared.request.precision) tables.outer.read tables.scalar.read tables.choice.read).read j))) =
      (BinaryPRGOutputPrimitiveWork.rescaleWithWork prepared.request.prepared.original.a
        (BinaryPRGOutputRun.fixedSample prepared.request rich prepared.request.precision
          (coinBitBudget n prepared.request.precision) tables.outer.read tables.scalar.read tables.choice.read).1).1 := by
    apply BinaryOverlapInputPreparation.table_ext
    intro j
    rw [BinaryPRGOutputPrimitiveWork.rescaleWithWork_state]
    simp only [FixedArrayTable.read_ofFn, BinaryPRGOriginalSampler.rescale]
    rw [← BinaryQuadraticData.apply_erasure,
      BinaryQuadraticOpcode.applyWithWork_state _ _ _ prepared.request.valid.2.1.1.1]
    · rw [hNormalized, hOld]
    · rw [hNormalized]
      exact (BinaryPRGResourceHandoff.fixedSample_canonical _ _ _ _ _ _ _ j).1
  unfold output BinaryPRGSeedBlockOutput.output
  dsimp only
  rw [hScale]

def run (rich : Bool) (frame seed : List Bool) : Option (List Bool) :=
  let decoded := BinaryPRGAccuracyRulerRequest.read frame
  decoded.1.bind (fun parsed =>
    if parsed.2 = [] then
      (BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.request.precision seed).1.map
        (output parsed.1.2 rich)
    else none)

theorem run_state (rich : Bool) (frame seed : List Bool) :
    run rich frame seed = (BinaryPRGOutputRun.run rich frame seed).map Prod.fst := by
  have h : run rich frame seed = (BinaryPRGSeedPreparedRun.run rich frame seed).1.map Prod.fst := by
    unfold run BinaryPRGSeedPreparedRun.run
    dsimp only
    cases hd : (BinaryPRGAccuracyRulerRequest.read frame).1 with
    | none => simp only [Option.bind_none, Option.map_none]
    | some parsed =>
        simp only [Option.bind_some]
        split
        · simp only [Option.map_map, Function.comp_def]
          congr 1
          funext tables
          exact output_state _ _ _
        · rfl
  exact h.trans (congrArg (Option.map Prod.fst) (BinaryPRGSeedPreparedRun.run_state rich frame seed))

theorem run_returned_budget (rich : Bool) (frame seed bytes : List Bool)
    (h : run rich frame seed = some bytes) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1, parsed.2.source⟩ : Σ n, RationalPRGOriginalInput n), parsed.2.accuracy, []) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) bytes := by
  rw [run_state] at h
  cases hOld : BinaryPRGOutputRun.run rich frame seed with
  | none => rw [hOld] at h; cases h
  | some returned =>
      rw [hOld, Option.map_some] at h
      cases Option.some.inj h
      exact BinaryPRGOutputRun.run_returned_budget rich frame seed returned hOld

end Blotto.BinaryPRGWordControllerFramed
