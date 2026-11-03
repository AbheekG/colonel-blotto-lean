import Blotto.BinaryTerminalPhysicalCompleteGeneratedMeasured
import Blotto.BinaryTerminalPhysicalAllowanceLaw

/-! The actual complete measured generated single/pair producers realize the
original fair-bit kernels and whole-allocation laws. Every path respects its
original hard budget, the pair law is the independent product, and strict
continuous-deviation regrets retain the original accuracy and model scope. -/

namespace Blotto.BinaryTerminalPhysicalCompleteGeneratedLaw
open MeasureTheory RationalLottoResourceSystem FreshBitSeedLifetime
set_option autoImplicit false

theorem kernel_operational (rich : Bool) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.kernel rich frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryTerminalPhysicalCompleteGeneratedMeasured.run
          (tapeFresh (vectorTape bits)) rich frame 0).1.1.1.1) := by
  simpa only [BinaryTerminalPhysicalCompleteGeneratedMeasured.run_data] using
    BinaryTerminalPhysicalOutputGenerated.kernel_operational rich frame prepared hRead f

theorem pairKernel_operational (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) × Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.pairKernel frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision+
        sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryTerminalPhysicalCompleteGeneratedMeasured.pair
          (tapeFresh (vectorTape bits)) frame 0).1.1.1.1) := by
  simpa only [BinaryTerminalPhysicalCompleteGeneratedMeasured.pair_data] using
    BinaryTerminalPhysicalOutputGenerated.pairKernel_operational frame prepared hRead f

def allocation (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    Fin prepared.1 → ℚ :=
  BinaryPRGSeedOutputLaw.readback prepared.1
    ((BinaryTerminalPhysicalCompleteGeneratedMeasured.run
      (tapeFresh (vectorTape bits)) rich frame 0).1.1.1.1.getD [])

theorem allocation_state (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    allocation frame prepared rich bits =
      BinaryTerminalPhysicalAllowanceLaw.allocation frame prepared rich bits := by
  simp only [allocation,BinaryTerminalPhysicalAllowanceLaw.allocation,
    BinaryTerminalPhysicalCompleteGeneratedMeasured.run_reference,BinaryTerminalPhysicalPreparedRaw.fresh_erases]

theorem every_path_fullBudget {S : Type*} (fresh : S → Bool × S) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (rich : Bool) (state : S) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ)
      else (prepared.2.request.source.b : ℝ))
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalCompleteGeneratedMeasured.run fresh rich frame state).1.1.1.1.getD []) j : ℝ)) := by
  rw [BinaryTerminalPhysicalCompleteGeneratedMeasured.run_reference,BinaryTerminalPhysicalPreparedRaw.fresh_erases]
  exact BinaryTerminalPhysicalAllowanceLaw.every_path_fullBudget fresh frame prepared hRead rich state

theorem pair_every_path_fullBudget {S : Type*} (fresh : S → Bool × S)
    (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (state : S) :
    FullBudget (prepared.2.request.source.a : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalCompleteGeneratedMeasured.pair fresh frame state).1.1.1.1.1.getD []) j : ℝ)) ∧
    FullBudget (prepared.2.request.source.b : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalCompleteGeneratedMeasured.pair fresh frame state).1.1.1.1.2.getD []) j : ℝ)) := by
  rw [BinaryTerminalPhysicalCompleteGeneratedMeasured.pair_reference,BinaryTerminalPhysicalPreparedRaw.pair_erases]
  exact BinaryTerminalPhysicalAllowanceLaw.pair_every_path_fullBudget fresh frame prepared hRead state

noncomputable def law (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) : Mixed prepared.1 :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (fun bits j => (allocation frame prepared rich bits j : ℝ))

theorem law_state (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) :
    law frame prepared rich = BinaryTerminalPhysicalAllowanceLaw.law frame prepared rich := by
  simp only [law,BinaryTerminalPhysicalAllowanceLaw.law,allocation_state]

def pairAllocation (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+
      sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    Allocation prepared.1 × Allocation prepared.1 :=
  let bytes := (BinaryTerminalPhysicalCompleteGeneratedMeasured.pair
    (tapeFresh (vectorTape bits)) frame 0).1.1.1.1
  ((fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.1.getD []) j : ℝ)),
    (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.2.getD []) j : ℝ)))

theorem pairAllocation_state (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+
      sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    pairAllocation frame prepared bits =
      BinaryTerminalPhysicalAllowanceLaw.pairAllocation frame prepared bits := by
  simp only [pairAllocation,BinaryTerminalPhysicalAllowanceLaw.pairAllocation,
    BinaryTerminalPhysicalCompleteGeneratedMeasured.pair_reference,BinaryTerminalPhysicalPreparedRaw.pair_erases]

noncomputable def pairLaw (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    ProbabilityMeasure (Allocation prepared.1 × Allocation prepared.1) :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision+
    sampleBitBudget prepared.1 prepared.2.request.precision)).map (pairAllocation frame prepared)

theorem pairLaw_state (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    pairLaw frame prepared = BinaryTerminalPhysicalAllowanceLaw.pairLaw frame prepared := by
  unfold pairLaw BinaryTerminalPhysicalAllowanceLaw.pairLaw
  congr 1
  funext bits
  exact pairAllocation_state frame prepared bits

theorem pairLaw_product (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    (pairLaw frame prepared : Measure (Allocation prepared.1 × Allocation prepared.1)) =
      (law frame prepared true : Measure (Allocation prepared.1)).prod
        (law frame prepared false : Measure (Allocation prepared.1)) := by
  rw [pairLaw_state,law_state,law_state]
  exact BinaryTerminalPhysicalAllowanceLaw.pairLaw_product frame prepared hRead

theorem law_regrets (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    regret prepared.2.request.source.realValues (prepared.2.request.source.a : ℝ)
      (law frame prepared true) (law frame prepared false) <
        prepared.2.request.accuracy.numeric.real ∧
    regret prepared.2.request.source.realValues (prepared.2.request.source.b : ℝ)
      (law frame prepared false) (law frame prepared true) <
        prepared.2.request.accuracy.numeric.real := by
  rw [law_state,law_state]
  exact BinaryTerminalPhysicalAllowanceLaw.law_regrets frame prepared hRead

end Blotto.BinaryTerminalPhysicalCompleteGeneratedLaw
