import Blotto.BinaryPRGHeapRequestWork
import Blotto.BinaryPRGWordControllerRawWorkBound

/-! Raw parsing, original-budget scaling and framing reach the physical
general-resource request backend. All terminal regimes keep the measured
continuations already proved by the controller request. -/

namespace Blotto.BinaryPRGHeapRawWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open RationalLottoResourceSystem

def outputWithWork {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) : List Bool × ℕ :=
  let store := BinarySeedLookupTree.prepare (List.ofFn tables.choice.read)
  let normalized := BinaryPRGHeapRequestWork.fixedSample store prepared.request rich
    prepared.request.precision tables.outer.read tables.scalar.read
  let scaled := BinaryPRGWordControllerFrameWork.rescaleWithWork prepared.request.prepared.original.a normalized.1
  let coordinates := List.ofFn scaled.1.read
  (prepared.header.bytes ++ BinaryStoredRowFrame.words coordinates,
    BinaryPRGWordControllerFrameWork.storePreparationWork tables + normalized.2 + scaled.2 +
      BinaryStoredRowFrameWork.wordsVisits coordinates + prepared.header.bytes.length + 2 * n + 3)

theorem outputWithWork_erasure {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputWithWork prepared rich tables).1 = BinaryPRGWordControllerFramed.output prepared rich tables := by
  unfold outputWithWork BinaryPRGWordControllerFramed.output
  dsimp only
  rw [BinaryPRGHeapRequestWork.fixedSample_erasure,
    BinaryPRGWordControllerFrameWork.rescaleWithWork_erasure]
  rfl

theorem output_work_compare {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    let store := BinarySeedLookupTree.prepare (List.ofFn tables.choice.read)
    (outputWithWork prepared rich tables).2 +
        (BinaryPRGWordControllerResourceWork.requestRun store prepared.request rich).2 =
      (BinaryPRGWordControllerRawWork.outputWithWork prepared rich tables).2 +
        (BinaryPRGHeapResourceRequest.run store prepared.request rich).2 := by
  let store := BinarySeedLookupTree.prepare (List.ofFn tables.choice.read)
  have hData := (BinaryPRGHeapRequestWork.fixedSample_erasure store prepared.request rich
    prepared.request.precision tables.outer.read tables.scalar.read).trans
    (BinaryPRGWordControllerRequestWork.fixedSample_erasure store prepared.request rich
      prepared.request.precision tables.outer.read tables.scalar.read).symm
  have hWork := BinaryPRGHeapRequestWork.fixedSample_work_compare store prepared.request rich
    prepared.request.precision tables.outer.read tables.scalar.read
  unfold outputWithWork BinaryPRGWordControllerRawWork.outputWithWork
  dsimp only
  change _ + (BinaryPRGWordControllerResourceWork.requestRun store prepared.request rich).2 =
    _ + (BinaryPRGHeapResourceRequest.run store prepared.request rich).2
  dsimp only [store] at hData hWork ⊢
  simp only [hData]
  omega

def run (rich : Bool) (frame seed : List Bool) : Option (List Bool) × ℕ :=
  let decoded := BinaryPRGAccuracyRulerRequest.read frame
  match decoded.1 with
  | none => (none,decoded.2.recorded + 1)
  | some parsed =>
      if parsed.2 = [] then
        let tables := BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.request.precision seed
        match tables.1 with
        | none => (none,decoded.2.recorded + tables.2.recorded + 3)
        | some stored =>
            let output := outputWithWork parsed.1.2 rich stored
            (some output.1,decoded.2.recorded + tables.2.recorded + output.2 + 3)
      else (none,decoded.2.recorded + 2)

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
        | some stored => simp only [Option.map_some,outputWithWork_erasure]
      · rfl

theorem run_returned_budget (rich : Bool) (frame seed bytes : List Bool)
    (h : (run rich frame seed).1 = some bytes) :
    ∃ parsed : Σ n,BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1,parsed.2.source⟩ : Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) bytes :=
  BinaryPRGWordControllerFramed.run_returned_budget rich frame seed bytes
    ((run_erasure rich frame seed).symm.trans h)

end Blotto.BinaryPRGHeapRawWork
