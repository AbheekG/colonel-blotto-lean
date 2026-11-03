import Blotto.RationalPRGRequestWorkBound

/-! Every successfully parsed request, including nonminimal encodings,
executes the same certified whole sampler on an exact-length seed. Budget
readback and both independent-law continuous-regret guarantees transfer. -/

namespace Blotto.RationalPRGBinaryRequest

theorem run_of_readWords (rich : Bool) (frame : List Bool) {n : ℕ}
    (i : RationalPRGOriginalInput n) (words : BinaryAccuracyWords)
    (h : readWords frame = some ((⟨n, i⟩ : Σ n, RationalPRGOriginalInput n), words, []))
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n words.precision) → Bool) :
    run rich frame (List.ofFn bits) =
      some (if rich then i.richOutputBits words.precision bits else i.poorOutputBits words.precision bits) := by
  have hBits : (FixedArrayTable.ofFn bits).read = bits := funext (fun j => FixedArrayTable.read_ofFn bits j)
  simp only [run, h, Option.bind_some, ite_true, seedTable_ofFn, Option.map_some, hBits]

theorem run_returned_budget_of_readWords (rich : Bool) (request : List Bool) {n : ℕ}
    (i : RationalPRGOriginalInput n) (words : BinaryAccuracyWords)
    (hRead : readWords request = some ((⟨n, i⟩ : Σ n, RationalPRGOriginalInput n), words, []))
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n words.precision) → Bool) (frame : List Bool)
    (h : run rich request (List.ofFn bits) = some frame) : ReturnedBudget n (if rich then i.a else i.b) frame := by
  rw [run_of_readWords rich request i words hRead bits] at h
  cases rich with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    cases Option.some.inj h
    exact ⟨List.ofFn (i.poorSample words.precision bits), by simpa using i.poorOutput_readback words.precision bits [],
      (i.output_readback_budgets words.precision bits).2⟩
  | true =>
    simp only [ite_true] at h ⊢
    cases Option.some.inj h
    exact ⟨List.ofFn (i.richSample words.precision bits), by simpa using i.richOutput_readback words.precision bits [],
      (i.output_readback_budgets words.precision bits).1⟩

theorem words_original_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (words : BinaryAccuracyWords) :
    regret i.realValues (i.a : ℝ) (i.richSampleLaw words.precision) (i.poorSampleLaw words.precision) < words.numeric.real ∧
      regret i.realValues (i.b : ℝ) (i.poorSampleLaw words.precision) (i.richSampleLaw words.precision) < words.numeric.real := by
  rw [words.precision_eq]
  exact words.numeric.original_regrets i

end Blotto.RationalPRGBinaryRequest
