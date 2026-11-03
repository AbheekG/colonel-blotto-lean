import Blotto.BinaryPRGBooleanFreshPairLifetime
import Blotto.BinaryPRGFreshRawLaw

/-! The selected physical-parser/Boolean-counter fresh runner preserves the
complete fresh-primitive expectations, every-path budgets, individual whole
laws, joint product measure and strict continuous regrets. Readback and
expectation semantics remain proof interpretation. -/
namespace Blotto.BinaryPRGBooleanFreshLaw
open MeasureTheory RationalLottoResourceSystem FreshBitSeedLifetime

theorem kernel_operational (rich : Bool) (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.kernel rich frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace (tapeFresh (vectorTape bits)) rich frame 0).1.1) := by
  simp only [BinaryTerminalPhysicalFreshRawLifetime.runWithTrace_state,
    BinaryPRGBooleanFreshRawLifetime.runWithTrace_state]
  exact BinaryPRGFreshRawLaw.kernel_operational rich frame prepared hRead f

theorem pairKernel_operational (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) × Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.pairKernel frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryPRGBooleanFreshPairLifetime.runWithTrace (tapeFresh (vectorTape bits)) frame 0).1.1) := by
  simp only [BinaryPRGBooleanFreshPairLifetime.runWithTrace_state]
  exact BinaryPRGFreshRawLaw.pairKernel_operational frame prepared hRead f

def allocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) : Fin prepared.1 → ℚ :=
  BinaryPRGSeedOutputLaw.readback prepared.1
    ((BinaryTerminalPhysicalFreshRawLifetime.runWithTrace (tapeFresh (vectorTape bits)) rich frame 0).1.1.getD [])

theorem allocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    allocation frame prepared rich bits = BinaryPRGFreshRawLaw.allocation frame prepared rich bits := by
  simp only [allocation,BinaryPRGFreshRawLaw.allocation,
    BinaryTerminalPhysicalFreshRawLifetime.runWithTrace_state,
    BinaryPRGBooleanFreshRawLifetime.runWithTrace_state]

theorem every_path_fullBudget {S : Type*} (fresh : S → Bool × S) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool) (state : S) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ) else (prepared.2.request.source.b : ℝ))
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh rich frame state).1.1.getD []) j : ℝ)) := by
  rw [BinaryTerminalPhysicalFreshRawLifetime.runWithTrace_state,
    BinaryPRGBooleanFreshRawLifetime.runWithTrace_state]
  exact BinaryPRGFreshRawLaw.every_path_fullBudget fresh frame prepared hRead rich state

theorem pair_every_path_fullBudget {S : Type*} (fresh : S → Bool × S)
    (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 =
      some (prepared,[])) (state : S) :
    FullBudget (prepared.2.request.source.a : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryPRGBooleanFreshPairLifetime.runWithTrace fresh frame state).1.1.1.getD []) j : ℝ)) ∧
    FullBudget (prepared.2.request.source.b : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryPRGBooleanFreshPairLifetime.runWithTrace fresh frame state).1.1.2.getD []) j : ℝ)) := by
  let rich := BinaryTerminalPhysicalFreshRawLifetime.runWithTrace
    fresh true frame state
  let poor := BinaryTerminalPhysicalFreshRawLifetime.runWithTrace
    fresh false frame rich.1.2
  have hRich := every_path_fullBudget fresh frame prepared hRead true state
  have hPoor := every_path_fullBudget fresh frame prepared hRead false rich.1.2
  change FullBudget _ (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
      (rich.1.1.getD []) j : ℝ)) ∧
    FullBudget _ (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
      (poor.1.1.getD []) j : ℝ))
  exact ⟨by simpa only [ite_true] using hRich,
    by simpa only [Bool.false_eq_true,ite_false] using hPoor⟩

noncomputable def law (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) : Mixed prepared.1 :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (fun bits j => (allocation frame prepared rich bits j : ℝ))

theorem law_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) :
    law frame prepared rich = BinaryPRGFreshRawLaw.law frame prepared rich := by
  simp only [law,BinaryPRGFreshRawLaw.law,allocation_state]

def pairAllocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    Allocation prepared.1 × Allocation prepared.1 :=
  let bytes := (BinaryPRGBooleanFreshPairLifetime.runWithTrace (tapeFresh (vectorTape bits)) frame 0).1.1
  ((fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.1.getD []) j : ℝ)),
    (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.2.getD []) j : ℝ)))

theorem pairAllocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    pairAllocation frame prepared bits = BinaryPRGFreshRawLaw.pairAllocation frame prepared bits := by
  simp only [pairAllocation,BinaryPRGFreshRawLaw.pairAllocation,BinaryPRGBooleanFreshPairLifetime.runWithTrace_state]

noncomputable def pairLaw (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    ProbabilityMeasure (Allocation prepared.1 × Allocation prepared.1) :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (pairAllocation frame prepared)

theorem pairLaw_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    pairLaw frame prepared = BinaryPRGFreshRawLaw.pairLaw frame prepared := by
  unfold pairLaw BinaryPRGFreshRawLaw.pairLaw
  congr 1
  funext bits
  exact pairAllocation_state frame prepared bits

theorem pairLaw_product (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    (pairLaw frame prepared : Measure (Allocation prepared.1 × Allocation prepared.1)) =
      (law frame prepared true : Measure (Allocation prepared.1)).prod (law frame prepared false : Measure (Allocation prepared.1)) := by
  rw [pairLaw_state,law_state,law_state]
  exact BinaryPRGFreshRawLaw.pairLaw_product frame prepared hRead

theorem law_regrets (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    regret prepared.2.request.source.realValues (prepared.2.request.source.a : ℝ)
      (law frame prepared true) (law frame prepared false) < prepared.2.request.accuracy.numeric.real ∧
    regret prepared.2.request.source.realValues (prepared.2.request.source.b : ℝ)
      (law frame prepared false) (law frame prepared true) < prepared.2.request.accuracy.numeric.real := by
  rw [law_state,law_state]
  exact BinaryPRGFreshRawLaw.law_regrets frame prepared hRead

end Blotto.BinaryPRGBooleanFreshLaw
