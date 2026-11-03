import Blotto.BinaryPRGSeedOutputLifetimePolynomial

/-! The actual validated seed-list/physical-output executor, on uniform full
finite bit vectors, always returns the original bytes. Interpreting those
serialized rows gives the original independent whole-allocation laws and
strict continuous-deviation regret bounds. Readback interpretation is not
additional work hidden in the output trace. -/
namespace Blotto.BinaryPRGSeedOutputLaw
open BinaryPRGHeapSeedOutputLifetime RationalLottoResourceSystem

theorem runWithTrace_ofFn {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget n prepared.request.precision) → Bool) :
    (runWithTrace prepared rich (List.ofFn bits)).1 = some (prepared.request.output rich bits) := by
  rw [runWithTrace_request,RationalPRGBinaryRequest.seedTable_ofFn]
  have hRead : (FixedArrayTable.ofFn bits).read = bits := funext (fun j => FixedArrayTable.read_ofFn bits j)
  simp only [Option.map_some,hRead]

theorem runWithTrace_wrong_length {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (seed : List Bool) (h : seed.length ≠ sampleBitBudget n prepared.request.precision) :
    (runWithTrace prepared rich seed).1 = none := by
  rw [runWithTrace_request,RationalPRGBinaryRequest.seedTable_wrong_length _ seed h,Option.map_none]

def readback (n : ℕ) (bytes : List Bool) : Fin n → ℚ := fun j =>
  match BinaryRatListFrame.readRow bytes with
  | none => 0
  | some row => row.2.1.getD j.val 0

def allocation {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget n prepared.request.precision) → Bool) : Fin n → ℚ :=
  readback n ((runWithTrace prepared rich (List.ofFn bits)).1.getD [])

theorem allocation_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget n prepared.request.precision) → Bool) :
    allocation prepared rich bits = if rich then prepared.request.source.richSample prepared.request.precision bits
      else prepared.request.source.poorSample prepared.request.precision bits := by
  unfold allocation
  rw [runWithTrace_ofFn,Option.getD_some]
  have h := prepared.request.output_read rich bits []
  simp only [List.append_nil] at h
  funext j
  simp [readback,h,List.getD_eq_getElem?_getD,j.isLt]

theorem allocation_fullBudget {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget n prepared.request.precision) → Bool) :
    FullBudget (if rich then (prepared.request.source.a : ℝ) else (prepared.request.source.b : ℝ))
      (fun j => (allocation prepared rich bits j : ℝ)) := by
  rw [allocation_state]
  cases rich
  · exact prepared.request.source.poorSample_fullBudget _ bits
  · exact prepared.request.source.richSample_fullBudget _ bits

noncomputable def law {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) : Mixed n :=
  (fairBitLaw (sampleBitBudget n prepared.request.precision)).map
    (fun bits j => (allocation prepared rich bits j : ℝ))

theorem law_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) :
    law prepared rich = if rich then prepared.request.source.richSampleLaw prepared.request.precision
      else prepared.request.source.poorSampleLaw prepared.request.precision := by
  cases rich <;> simp only [law,allocation_state,Bool.false_eq_true,ite_false,ite_true,
    RationalPRGOriginalInput.richSampleLaw,RationalPRGOriginalInput.poorSampleLaw]

theorem law_regrets {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) :
    regret prepared.request.source.realValues (prepared.request.source.a : ℝ) (law prepared true) (law prepared false) <
      prepared.request.accuracy.numeric.real ∧
    regret prepared.request.source.realValues (prepared.request.source.b : ℝ) (law prepared false) (law prepared true) <
      prepared.request.accuracy.numeric.real := by
  have h := prepared.request.regrets
  rw [BinaryPRGOriginalSampler.richSampleLaw_refines,BinaryPRGOriginalSampler.poorSampleLaw_refines] at h
  simpa only [law_state,ite_true,Bool.false_eq_true,ite_false,BinaryPRGRequest.Request.source] using h

end Blotto.BinaryPRGSeedOutputLaw
