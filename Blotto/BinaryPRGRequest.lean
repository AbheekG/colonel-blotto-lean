import Blotto.BinaryPRGFrame
import Blotto.BinaryStoredRowFrame
import Blotto.RationalPRGBinaryRequest

/-! End-to-end native stored-word PRG request interface. Parsing checks the
original game and positive accuracy words, computes precision once, and keeps
the prepared arrays for repeated independent draws. The convenience runner
rejects trailing request bits and wrong seed lengths, then writes a row directly
from stored output words. Semantic sources occur only in proofs. Complete
preparation, draw, interface/backend and physical-space prices remain separate. -/

namespace Blotto.BinaryPRGRequest
open BinaryRationalNormalization BinaryPRGPreparation

structure Request (n : ℕ) where
  prepared : Prepared n
  valid : prepared.Valid
  accuracy : BinaryAccuracyWords
  precision : ℕ
  precision_eq : precision = accuracy.precision

def read (bits : List Bool) : Option ((Σ n, Request n) × List Bool) :=
  (BinaryPRGFrame.readChecked bits).bind (fun game =>
    (BinaryAccuracyWords.read game.2).map (fun accuracy =>
      (⟨game.1.1, ⟨game.1.2.val, game.1.2.property, accuracy.1, accuracy.1.precision, rfl⟩⟩, accuracy.2)))

noncomputable def Request.source {n : ℕ} (request : Request n) : RationalPRGOriginalInput n :=
  request.prepared.original.source request.valid.2.2

noncomputable def decoded (request : Σ n, Request n) :
    (Σ n, RationalPRGOriginalInput n) × BinaryAccuracyWords :=
  (⟨request.1, request.2.source⟩, request.2.accuracy)

theorem read_refines (bits : List Bool) :
    (read bits).map (fun result => ((decoded result.1).1, (decoded result.1).2, result.2)) =
      RationalPRGBinaryRequest.readWords bits := by
  have hg := BinaryPRGFrame.readChecked_refines bits
  cases hr : BinaryPRGFrame.readChecked bits with
  | none =>
      rw [hr, Option.map_none] at hg
      simp only [read, hr, Option.bind_none, Option.map_none, RationalPRGBinaryRequest.readWords, ← hg]
  | some game =>
      rw [hr, Option.map_some] at hg
      simp only [read, hr, Option.bind_some, RationalPRGBinaryRequest.readWords, ← hg, Option.bind_some]
      cases ha : BinaryAccuracyWords.read game.2 with
      | none => rfl
      | some accuracy => rfl

theorem read_numeric_refines (bits : List Bool) :
    (read bits).map (fun result => ((decoded result.1).1, (decoded result.1).2.numeric, result.2)) =
      RationalPRGBinaryRequest.read bits := by
  have hw := read_refines bits
  have hn := RationalPRGBinaryRequest.readWords_numeric_eq bits
  cases hr : read bits with
  | none =>
      rw [hr, Option.map_none] at hw
      rw [← hw, Option.map_none] at hn
      exact hn
  | some parsed =>
      rw [hr, Option.map_some] at hw
      rw [← hw, Option.map_some] at hn
      exact hn

theorem read_encoded {n : ℕ} (input : RationalPRGOriginalInput n) (accuracy : BinaryAccuracyInput)
    (suffix : List Bool) :
    ∃ parsed : Σ m, Request m,
      read (RationalPRGBinaryRequest.encode input accuracy ++ suffix) = some (parsed, suffix) ∧
      (decoded parsed).1 = (⟨n, input⟩ : Σ m, RationalPRGOriginalInput m) ∧
      parsed.2.accuracy.numeric = accuracy := by
  have hr := read_numeric_refines (RationalPRGBinaryRequest.encode input accuracy ++ suffix)
  rw [RationalPRGBinaryRequest.read_encode_append] at hr
  cases hs : read (RationalPRGBinaryRequest.encode input accuracy ++ suffix) with
  | none => rw [hs, Option.map_none] at hr; cases hr
  | some parsed =>
      rw [hs, Option.map_some] at hr
      have he := Option.some.inj hr
      have hg := congrArg Prod.fst he
      have ha := congrArg (fun result => result.2.1) he
      have ht := congrArg (fun result => result.2.2) he
      change parsed.2 = suffix at ht
      refine ⟨parsed.1, ?_, hg, ha⟩
      exact congrArg (fun tail => some (parsed.1, tail)) ht

def Request.richSample {n : ℕ} (request : Request n)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FixedArrayTable n BinaryRationalNormalization.SignedWord :=
  BinaryPRGOriginalSampler.richSample request.prepared request.valid request.precision bits

def Request.poorSample {n : ℕ} (request : Request n)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FixedArrayTable n BinaryRationalNormalization.SignedWord :=
  BinaryPRGOriginalSampler.poorSample request.prepared request.valid request.precision bits

def Request.output {n : ℕ} (request : Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) : List Bool :=
  if rich then BinaryStoredRowFrame.row (request.richSample bits) else BinaryStoredRowFrame.row (request.poorSample bits)

theorem Request.sample_budgets {n : ℕ} (request : Request n)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FullBudget (value request.prepared.original.a : ℝ)
      (fun j => (value ((request.richSample bits).read j) : ℝ)) ∧
    FullBudget (value request.prepared.original.b : ℝ)
      (fun j => (value ((request.poorSample bits).read j) : ℝ)) :=
  ⟨BinaryPRGOriginalSampler.richSample_fullBudget _ _ _ bits,
    BinaryPRGOriginalSampler.poorSample_fullBudget _ _ _ bits⟩

theorem Request.sample_canonical {n : ℕ} (request : Request n)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (∀ j, BinaryRationalEncoding.CanonicalWord ((request.richSample bits).read j)) ∧
    (∀ j, BinaryRationalEncoding.CanonicalWord ((request.poorSample bits).read j)) :=
  ⟨BinaryPRGOriginalSampler.richSample_canonical _ _ _ bits,
    BinaryPRGOriginalSampler.poorSample_canonical _ _ _ bits⟩

theorem Request.regrets {n : ℕ} (request : Request n) :
    regret request.source.realValues (request.source.a : ℝ)
      (BinaryPRGOriginalSampler.richSampleLaw request.prepared request.valid request.precision)
      (BinaryPRGOriginalSampler.poorSampleLaw request.prepared request.valid request.precision) < request.accuracy.numeric.real ∧
    regret request.source.realValues (request.source.b : ℝ)
      (BinaryPRGOriginalSampler.poorSampleLaw request.prepared request.valid request.precision)
      (BinaryPRGOriginalSampler.richSampleLaw request.prepared request.valid request.precision) < request.accuracy.numeric.real := by
  rw [request.precision_eq]
  exact BinaryPRGOriginalSampler.stored_accuracy_regrets request.prepared request.valid request.accuracy

theorem Request.output_read {n : ℕ} (request : Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (request.output rich bits ++ suffix) =
      some (n, List.ofFn (if rich then request.source.richSample request.precision bits
        else request.source.poorSample request.precision bits), suffix) := by
  cases rich
  · exact BinaryStoredRowFrame.poorOutput_read request.prepared request.valid request.precision bits suffix
  · exact BinaryStoredRowFrame.richOutput_read request.prepared request.valid request.precision bits suffix

theorem Request.output_returned_budget {n : ℕ} (request : Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    RationalPRGBinaryRequest.ReturnedBudget n (if rich then request.source.a else request.source.b)
      (request.output rich bits) := by
  cases rich
  · exact ⟨List.ofFn (request.source.poorSample request.precision bits),
      by simpa only [List.append_nil, Bool.false_eq_true, ite_false] using request.output_read false bits [],
      (request.source.output_readback_budgets request.precision bits).2⟩
  · exact ⟨List.ofFn (request.source.richSample request.precision bits),
      by simpa only [List.append_nil, ite_true] using request.output_read true bits [],
      (request.source.output_readback_budgets request.precision bits).1⟩

def run (rich : Bool) (request seed : List Bool) : Option (List Bool) :=
  (read request).bind (fun parsed =>
    if parsed.2 = [] then
      (RationalPRGBinaryRequest.seedTable
        (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.precision) seed).map
          (fun table => parsed.1.2.output rich table.read)
    else none)

theorem run_success (rich : Bool) (request seed frame : List Bool)
    (h : run rich request seed = some frame) :
    ∃ parsed : Σ n, Request n,
      read request = some (parsed, []) ∧
      ∃ table : FixedArrayTable (RationalLottoResourceSystem.sampleBitBudget parsed.1 parsed.2.precision) Bool,
        RationalPRGBinaryRequest.seedTable
          (RationalLottoResourceSystem.sampleBitBudget parsed.1 parsed.2.precision) seed = some table ∧
        frame = parsed.2.output rich table.read := by
  unfold run at h
  cases hr : read request with
  | none => rw [hr, Option.bind_none] at h; cases h
  | some parsed =>
      rw [hr, Option.bind_some] at h
      split at h
      · rename_i hTail
        cases hs : RationalPRGBinaryRequest.seedTable
            (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.precision) seed with
        | none => rw [hs, Option.map_none] at h; cases h
        | some table =>
            rw [hs, Option.map_some] at h
            refine ⟨parsed.1, ?_, table, hs, (Option.some.inj h).symm⟩
            exact congrArg (fun tail => some (parsed.1, tail)) hTail
      · cases h

theorem run_returned_budget (rich : Bool) (request seed frame : List Bool)
    (h : run rich request seed = some frame) :
    ∃ parsed : Σ n, Request n,
      RationalPRGBinaryRequest.readWords request =
        some ((⟨parsed.1, parsed.2.source⟩ : Σ n, RationalPRGOriginalInput n), parsed.2.accuracy, []) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) frame := by
  obtain ⟨parsed, hr, table, _, hFrame⟩ := run_success rich request seed frame h
  refine ⟨parsed, ?_, ?_⟩
  · have he := read_refines request
    rw [hr, Option.map_some] at he
    exact he.symm
  · rw [hFrame]
    exact parsed.2.output_returned_budget rich table.read

end Blotto.BinaryPRGRequest
