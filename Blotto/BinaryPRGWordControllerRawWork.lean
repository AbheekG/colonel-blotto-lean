import Blotto.BinaryPRGWordControllerRequestWork
import Blotto.BinaryPRGWordControllerFrameWork

/-! The raw request joins its unchanged measured parser/accuracy/seed stages
with actual seed-Store production, the concrete Boolean-PC source draw, global
fallback, quadratic original-budget scaling and coordinate framing.  Work is
the declared Boolean/list/copy/controller source ledger.  Full physical table
addresses, small scalar representation and compiler interpretation remain
explicitly outside that model and are not inferred from identical bytes. -/

namespace Blotto.BinaryPRGWordControllerRawWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open RationalLottoResourceSystem BinaryPRGOutputPrimitiveWork

def outputWithWork {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) : List Bool × ℕ :=
  let store := BinarySeedLookupTree.prepare (List.ofFn tables.choice.read)
  let normalized := BinaryPRGWordControllerRequestWork.fixedSample store prepared.request rich
    prepared.request.precision tables.outer.read tables.scalar.read
  let scaled := BinaryPRGWordControllerFrameWork.rescaleWithWork prepared.request.prepared.original.a normalized.1
  let coordinates := List.ofFn scaled.1.read
  (prepared.header.bytes ++ BinaryStoredRowFrame.words coordinates,
    BinaryPRGWordControllerFrameWork.storePreparationWork tables + normalized.2 + scaled.2 +
      BinaryStoredRowFrameWork.wordsVisits coordinates + prepared.header.bytes.length + 2 * n + 3)

theorem outputWithWork_erasure {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputWithWork prepared rich tables).1 = BinaryPRGWordControllerFramed.output prepared rich tables := by
  unfold outputWithWork BinaryPRGWordControllerFramed.output
  dsimp only
  rw [BinaryPRGWordControllerRequestWork.fixedSample_erasure,
    BinaryPRGWordControllerFrameWork.rescaleWithWork_erasure]
  rfl

theorem fixedBound_index_mono {n : ℕ} (request : BinaryPRGRequest.Request n) (K N : ℕ)
    {first second : ℕ} (h : first ≤ second) :
    BinaryPRGWordControllerRequestWork.fixedBound request K first N ≤
      BinaryPRGWordControllerRequestWork.fixedBound request K second N := by
  simp only [BinaryPRGWordControllerRequestWork.fixedBound, BinaryPRGWordControllerRequestWork.bound,
    BinaryPRGWordControllerResourceWork.initialBound,
    BinaryPRGWordControllerBooleanResourceSourceWork.initialBound,
    BinaryPRGWordControllerBooleanResourceLoopWork.bound,
    BinaryPRGWordControllerBooleanResourceLoopWork.pairBound,
    BinaryPRGWordControllerResourceWork.bound,
    BinaryPRGWordControllerResourceWork.pairBound, BinaryPRGWordControllerResource.bodyBound,
    BinaryPRGWordControllerTerminalWork.bound, BinaryPRGWordControllerGroupWork.uniformBound,
    BinaryPRGWordControllerGroupWork.mixedBound, BinaryPRGWordControllerFourWork.restoredBound,
    BinaryPRGWordControllerFourWork.runBound, BinaryPRGWordControllerFourWork.gluingBound,
    BinaryPRGWordControllerFourWork.smallBound, BinaryPRGWordControllerFourWork.rootBound,
    BinaryPRGWordControllerFourWork.uniformBound, BinaryPRGWordControllerReflectedWork.bound,
    BinaryPRGWordControllerReflectedWork.selectionBound, BinaryPRGWordControllerReflectedSetupWork.bound,
    BinaryPRGWordControllerBooleanResourceThreeWork.sourceBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.sourceEnvelope,
    BinaryPRGWordControllerBooleanResourceThreeWork.bound,
    BinaryPRGWordControllerBooleanResourceThreeWork.pairBound,
    BinaryPRGWordControllerThreeResourceWork.bound, BinaryPRGWordControllerThreeResourceWork.pairBound,
    BinaryPRGWordControllerThreeResource.bodyBound, BinaryPRGWordControllerWork.segmentBound,
    BinaryPRGWordControllerWork.selectionBound, BinaryWordIndexCoinController.allowance]
  gcongr

noncomputable def outputBound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) : ℕ :=
  36 * coinBitBudget n prepared.request.precision + 7 +
    BinaryPRGWordControllerRequestWork.fixedBound prepared.request prepared.request.precision
      (binaryWordWidth (coinBitBudget n prepared.request.precision)) (coinBitBudget n prepared.request.precision) +
        BinaryPRGWordControllerFrameWork.suffixBound prepared

theorem outputWithWork_bound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputWithWork prepared rich tables).2 ≤ outputBound prepared := by
  let store := BinarySeedLookupTree.prepare (List.ofFn tables.choice.read)
  have hDraw := BinaryPRGWordControllerRequestWork.fixedSample_bound store prepared.request rich
    prepared.request.precision tables.outer.read tables.scalar.read
  have hWidth := BinarySeedLookupTree.prepare_width_bound (List.ofFn tables.choice.read)
  rw [List.length_ofFn] at hWidth
  have hCap : store.cap.value = coinBitBudget n prepared.request.precision := by
    dsimp only [store]
    rw [BinarySeedLookupTree.cap_value, List.length_ofFn]
  rw [hCap] at hDraw
  have hDraw' := hDraw.trans (fixedBound_index_mono prepared.request prepared.request.precision
    (coinBitBudget n prepared.request.precision) hWidth)
  have hStore := BinaryPRGWordControllerFrameWork.storePreparationWork_bound tables
  have hSuffix := BinaryPRGWordControllerFrameWork.outputSuffixWithWork_bound prepared rich tables
  unfold outputWithWork outputBound
  dsimp only
  rw [BinaryPRGWordControllerRequestWork.fixedSample_erasure]
  change BinaryPRGWordControllerFrameWork.storePreparationWork tables +
    (BinaryPRGWordControllerRequestWork.fixedSample store prepared.request rich prepared.request.precision
      tables.outer.read tables.scalar.read).2 +
        (BinaryPRGWordControllerFrameWork.rescaleWithWork prepared.request.prepared.original.a
          (BinaryPRGWordControllerFrameWork.normalized prepared rich tables)).2 +
          BinaryStoredRowFrameWork.wordsVisits (List.ofFn
            (BinaryPRGWordControllerFrameWork.rescaleWithWork prepared.request.prepared.original.a
              (BinaryPRGWordControllerFrameWork.normalized prepared rich tables)).1.read) +
            prepared.header.bytes.length + 2 * n + 3 ≤ _
  unfold BinaryPRGWordControllerFrameWork.outputSuffixWithWork at hSuffix
  dsimp only at hSuffix
  omega

def run (rich : Bool) (frame seed : List Bool) : Option (List Bool) × ℕ :=
  let decoded := BinaryPRGAccuracyRulerRequest.read frame
  match decoded.1 with
  | none => (none, decoded.2.recorded + 1)
  | some parsed =>
      if parsed.2 = [] then
        let tables := BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.request.precision seed
        match tables.1 with
        | none => (none, decoded.2.recorded + tables.2.recorded + 3)
        | some stored =>
            let output := outputWithWork parsed.1.2 rich stored
            (some output.1, decoded.2.recorded + tables.2.recorded + output.2 + 3)
      else (none, decoded.2.recorded + 2)

theorem run_erasure (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).1 = BinaryPRGWordControllerFramed.run rich frame seed := by
  unfold run BinaryPRGWordControllerFramed.run
  dsimp only
  cases hd : (BinaryPRGAccuracyRulerRequest.read frame).1 with
  | none => rfl
  | some parsed =>
      simp only [Option.bind_some]
      split
      · cases hs : (BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.request.precision seed).1 with
        | none => rfl
        | some stored => simp only [Option.map_some, outputWithWork_erasure]
      · rfl

theorem run_returned_budget (rich : Bool) (frame seed bytes : List Bool)
    (h : (run rich frame seed).1 = some bytes) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1, parsed.2.source⟩ : Σ n, RationalPRGOriginalInput n), parsed.2.accuracy, []) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) bytes :=
  BinaryPRGWordControllerFramed.run_returned_budget rich frame seed bytes ((run_erasure rich frame seed).symm.trans h)

end Blotto.BinaryPRGWordControllerRawWork
