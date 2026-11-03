import Blotto.BinaryPRGFreshPairLifetime
import Blotto.FreshBitSeedKernel
import Blotto.FairBitProductLaw

/-! Actual generated seed lists and actual raw byte execution have the old
whole-allocation laws. The sequential pair has their product measure, with
strict continuous-deviation regret bounds. The random primitive is a named
fresh independent fair Boolean; no physical entropy implementation or host
compiler theorem is inferred. Readback remains a semantic interpretation. -/
namespace Blotto.BinaryPRGFreshRawLaw
open MeasureTheory RationalLottoResourceSystem FreshBitSeedLifetime
set_option maxHeartbeats 3000000

-- Recursive fresh-primitive semantics of the executable request gates.
noncomputable def kernel (rich : Bool) (frame : List Bool) : BoundedExpectationKernel (Option (List Bool)) :=
  match (BinaryPRGRawRequestLifetime.readWithTrace frame).1 with
  | none => BoundedExpectationKernel.point none
  | some parsed =>
      if parsed.2 = [] then
        (FreshBitSeedKernel.generate (sampleBitBudget parsed.1.1 parsed.1.2.request.precision)).map
          (fun seed => (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed).1)
      else BoundedExpectationKernel.point none

theorem kernel_accepted (rich : Bool) (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) → ℝ) :
    (kernel rich frame).mean f = (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision)).mean
      (fun bits => f (some (prepared.2.request.output rich bits))) := by
  simp only [kernel,hRead,ite_true,BoundedExpectationKernel.map,BoundedExpectationKernel.bind,
    BoundedExpectationKernel.point,FreshBitSeedKernel.generate_mean,BinaryPRGSeedOutputLaw.runWithTrace_ofFn]

theorem kernel_operational (rich : Bool) (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) → ℝ) :
    (kernel rich frame).mean f = (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision)).mean
      (fun bits => f (BinaryPRGFreshRawLifetime.runWithTrace (tapeFresh (vectorTape bits)) rich frame 0).1.1) := by
  simp only [BinaryPRGFreshRawLifetime.runWithTrace_vector rich frame prepared hRead,kernel_accepted rich frame prepared hRead]

noncomputable def pairKernel (frame : List Bool) : BoundedExpectationKernel (Option (List Bool) × Option (List Bool)) :=
  (kernel true frame).bind (fun rich => (kernel false frame).map (fun poor => (rich,poor)))

theorem pairKernel_operational (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) × Option (List Bool) → ℝ) :
    (pairKernel frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryPRGFreshPairLifetime.runWithTrace (tapeFresh (vectorTape bits)) frame 0).1.1) := by
  simp only [pairKernel,BoundedExpectationKernel.bind,BoundedExpectationKernel.map,BoundedExpectationKernel.point]
  rw [kernel_accepted true frame prepared hRead]
  simp_rw [kernel_accepted false frame prepared hRead]
  rw [← fairBitKernel_blocks]
  simp only [BinaryPRGFreshPairLifetime.runWithTrace_vector frame prepared hRead]

def allocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) : Fin prepared.1 → ℚ :=
  BinaryPRGSeedOutputLaw.readback prepared.1
    ((BinaryPRGFreshRawLifetime.runWithTrace (tapeFresh (vectorTape bits)) rich frame 0).1.1.getD [])

theorem allocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    allocation frame prepared rich bits = BinaryPRGSeedOutputLaw.allocation prepared.2 rich bits := by
  simp only [allocation,BinaryPRGFreshRawLifetime.runWithTrace_vector rich frame prepared hRead,
    BinaryPRGSeedOutputLaw.allocation,BinaryPRGSeedOutputLaw.runWithTrace_ofFn]

theorem allocation_fullBudget (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ) else (prepared.2.request.source.b : ℝ))
      (fun j => (allocation frame prepared rich bits j : ℝ)) := by
  rw [allocation_state frame prepared hRead rich bits]
  exact BinaryPRGSeedOutputLaw.allocation_fullBudget prepared.2 rich bits

theorem every_path_fullBudget {S : Type*} (fresh : S → Bool × S) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool) (state : S) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ) else (prepared.2.request.source.b : ℝ))
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryPRGFreshRawLifetime.runWithTrace fresh rich frame state).1.1.getD []) j : ℝ)) := by
  obtain ⟨bits,hBits⟩ := BinaryPRGFreshRawLifetime.accepted_returns fresh rich frame prepared hRead state
  rw [hBits]
  have h := BinaryPRGSeedOutputLaw.allocation_fullBudget prepared.2 rich bits
  simpa only [BinaryPRGSeedOutputLaw.allocation,BinaryPRGSeedOutputLaw.runWithTrace_ofFn,Option.getD_some] using h

noncomputable def law (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) : Mixed prepared.1 :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (fun bits j => (allocation frame prepared rich bits j : ℝ))

theorem law_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool) :
    law frame prepared rich = BinaryPRGSeedOutputLaw.law prepared.2 rich := by
  simp only [law,BinaryPRGSeedOutputLaw.law,allocation_state frame prepared hRead rich]

def pairAllocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    Allocation prepared.1 × Allocation prepared.1 :=
  let bytes := (BinaryPRGFreshPairLifetime.runWithTrace (tapeFresh (vectorTape bits)) frame 0).1.1
  ((fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.1.getD []) j : ℝ)),
    (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.2.getD []) j : ℝ)))

theorem pairAllocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    pairAllocation frame prepared bits =
      ((fun j => (allocation frame prepared true (firstBitBlock _ _ bits) j : ℝ)),
        (fun j => (allocation frame prepared false (secondBitBlock _ _ bits) j : ℝ))) := by
  simp only [pairAllocation,BinaryPRGFreshPairLifetime.runWithTrace_vector frame prepared hRead,
    allocation,BinaryPRGFreshRawLifetime.runWithTrace_vector true frame prepared hRead,
    BinaryPRGFreshRawLifetime.runWithTrace_vector false frame prepared hRead]

theorem pairAllocation_fullBudgets (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    FullBudget (prepared.2.request.source.a : ℝ) (pairAllocation frame prepared bits).1 ∧
    FullBudget (prepared.2.request.source.b : ℝ) (pairAllocation frame prepared bits).2 := by
  rw [pairAllocation_state frame prepared hRead bits]
  exact ⟨allocation_fullBudget frame prepared hRead true _,allocation_fullBudget frame prepared hRead false _⟩

noncomputable def pairLaw (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    ProbabilityMeasure (Allocation prepared.1 × Allocation prepared.1) :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (pairAllocation frame prepared)

theorem pairLaw_product (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    (pairLaw frame prepared : Measure (Allocation prepared.1 × Allocation prepared.1)) =
      (law frame prepared true : Measure (Allocation prepared.1)).prod (law frame prepared false : Measure (Allocation prepared.1)) := by
  have hPair : pairAllocation frame prepared = fun bits =>
      ((fun j => (allocation frame prepared true (firstBitBlock _ _ bits) j : ℝ)),
        (fun j => (allocation frame prepared false (secondBitBlock _ _ bits) j : ℝ))) :=
    funext (pairAllocation_state frame prepared hRead)
  simp only [pairLaw,ProbabilityMeasure.toMeasure_map,hPair,law]
  exact fairBitBlocks_map_product (sampleBitBudget prepared.1 prepared.2.request.precision)
    (sampleBitBudget prepared.1 prepared.2.request.precision)
    (fun bits j => (allocation frame prepared true bits j : ℝ))
    (fun bits j => (allocation frame prepared false bits j : ℝ))

theorem law_regrets (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    regret prepared.2.request.source.realValues (prepared.2.request.source.a : ℝ)
      (law frame prepared true) (law frame prepared false) < prepared.2.request.accuracy.numeric.real ∧
    regret prepared.2.request.source.realValues (prepared.2.request.source.b : ℝ)
      (law frame prepared false) (law frame prepared true) < prepared.2.request.accuracy.numeric.real := by
  rw [law_state frame prepared hRead true,law_state frame prepared hRead false]
  exact BinaryPRGSeedOutputLaw.law_regrets prepared.2

end Blotto.BinaryPRGFreshRawLaw
