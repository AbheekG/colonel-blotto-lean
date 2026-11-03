import Blotto.BinaryPRGFullRawLifetime

/-! Uniform finite seeds interpreted through the complete actual raw
request/seed/output executor recover the original whole-allocation laws.
Successful raw reading supplies the exact prepared request; readback is a
semantic interpretation, not additional unpriced output-producer work. -/
namespace Blotto.BinaryPRGFullRawLaw
open RationalLottoResourceSystem

def allocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) : Fin prepared.1 → ℚ :=
  BinaryPRGSeedOutputLaw.readback prepared.1 ((BinaryPRGFullRawLifetime.runWithTrace rich frame (List.ofFn bits)).1.getD [])

theorem allocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    allocation frame prepared rich bits = BinaryPRGSeedOutputLaw.allocation prepared.2 rich bits := by
  unfold allocation BinaryPRGSeedOutputLaw.allocation
  rw [BinaryPRGFullRawLifetime.runWithTrace_ofFn frame prepared hRead rich bits,BinaryPRGSeedOutputLaw.runWithTrace_ofFn]

theorem allocation_fullBudget (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ) else (prepared.2.request.source.b : ℝ))
      (fun j => (allocation frame prepared rich bits j : ℝ)) := by
  rw [allocation_state frame prepared hRead rich bits]
  exact BinaryPRGSeedOutputLaw.allocation_fullBudget prepared.2 rich bits

theorem output_read (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (((BinaryPRGFullRawLifetime.runWithTrace rich frame (List.ofFn bits)).1.getD [])++suffix) =
      some (prepared.1,List.ofFn (if rich then prepared.2.request.source.richSample prepared.2.request.precision bits
        else prepared.2.request.source.poorSample prepared.2.request.precision bits),suffix) := by
  rw [BinaryPRGFullRawLifetime.runWithTrace_ofFn frame prepared hRead rich bits,Option.getD_some]
  exact prepared.2.request.output_read rich bits suffix

noncomputable def law (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) : Mixed prepared.1 :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (fun bits j => (allocation frame prepared rich bits j : ℝ))

theorem law_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool) :
    law frame prepared rich = BinaryPRGSeedOutputLaw.law prepared.2 rich := by
  simp only [law,BinaryPRGSeedOutputLaw.law,allocation_state frame prepared hRead rich]

theorem law_regrets (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    regret prepared.2.request.source.realValues (prepared.2.request.source.a : ℝ)
      (law frame prepared true) (law frame prepared false) < prepared.2.request.accuracy.numeric.real ∧
    regret prepared.2.request.source.realValues (prepared.2.request.source.b : ℝ)
      (law frame prepared false) (law frame prepared true) < prepared.2.request.accuracy.numeric.real := by
  rw [law_state frame prepared hRead true,law_state frame prepared hRead false]
  exact BinaryPRGSeedOutputLaw.law_regrets prepared.2

end Blotto.BinaryPRGFullRawLaw
