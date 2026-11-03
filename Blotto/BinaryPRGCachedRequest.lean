import Blotto.BinaryPRGCachedSampler

/-! The complete framed PRG runner uses cached terminal preparation on every
draw, with exact output-byte equality to the retained original interface on
arbitrary request/seed strings. Reusable typed request draws and independent
law guarantees come from BinaryPRGCachedSampler. Full computational-model cost
and ownership/storage contracts remain separate from this interface refinement. -/

namespace Blotto.BinaryPRGCachedRequest
open BinaryRationalNormalization

def output {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) : List Bool :=
  BinaryStoredRowFrame.row (BinaryPRGCachedSampler.originalSample request rich bits).1

theorem output_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    output request rich bits = request.output rich bits := by
  unfold output
  rw [BinaryPRGCachedSampler.originalSample_state]
  cases rich <;> rfl

def run (rich : Bool) (request seed : List Bool) : Option (List Bool) :=
  (BinaryPRGRequest.read request).bind (fun parsed =>
    if parsed.2 = [] then
      (RationalPRGBinaryRequest.seedTable
        (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.precision) seed).map
          (fun table => output parsed.1.2 rich table.read)
    else none)

theorem run_state (rich : Bool) (request seed : List Bool) :
    run rich request seed = BinaryPRGRequest.run rich request seed := by
  unfold run BinaryPRGRequest.run
  simp only [output_state]

theorem run_returned_budget (rich : Bool) (request seed frame : List Bool)
    (h : run rich request seed = some frame) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords request =
        some ((⟨parsed.1, parsed.2.source⟩ : Σ n, RationalPRGOriginalInput n), parsed.2.accuracy, []) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) frame := by
  rw [run_state] at h
  exact BinaryPRGRequest.run_returned_budget rich request seed frame h

end Blotto.BinaryPRGCachedRequest
