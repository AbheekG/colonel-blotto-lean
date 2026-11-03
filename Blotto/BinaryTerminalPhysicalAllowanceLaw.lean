import Blotto.BinaryTerminalPhysicalAllowanceFresh
import Blotto.BinaryPRGBooleanFreshLaw

/-! Exact operational fair-bit kernels, hard budgets on every path and whole
allocation laws for the encoded-allowance route. The product and strict regret
claims retain the established independent fair-bit primitive model. -/

namespace Blotto.BinaryTerminalPhysicalAllowanceLaw
open MeasureTheory RationalLottoResourceSystem FreshBitSeedLifetime
set_option autoImplicit false

theorem kernel_operational (rich : Bool) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.kernel rich frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryTerminalPhysicalAllowanceFresh.run
          (tapeFresh (vectorTape bits)) rich frame 0).1.1.1.1) := by
  simpa only [BinaryTerminalPhysicalAllowanceFresh.run_data] using
    BinaryPRGBooleanFreshLaw.kernel_operational rich frame prepared hRead f

theorem pairKernel_operational (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) × Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.pairKernel frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision+
        sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryTerminalPhysicalAllowanceFresh.pair
          (tapeFresh (vectorTape bits)) frame 0).1.1.1.1) := by
  simpa only [BinaryTerminalPhysicalAllowanceFresh.pair_data] using
    BinaryPRGBooleanFreshLaw.pairKernel_operational frame prepared hRead f

def allocation (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    Fin prepared.1 → ℚ :=
  BinaryPRGSeedOutputLaw.readback prepared.1
    ((BinaryTerminalPhysicalAllowanceFresh.run
      (tapeFresh (vectorTape bits)) rich frame 0).1.1.1.1.getD [])

theorem allocation_state (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    allocation frame prepared rich bits =
      BinaryPRGBooleanFreshLaw.allocation frame prepared rich bits := by
  simp only [allocation,BinaryPRGBooleanFreshLaw.allocation,
    BinaryTerminalPhysicalAllowanceFresh.run_data]

theorem every_path_fullBudget {S : Type*} (fresh : S → Bool × S) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (rich : Bool) (state : S) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ)
      else (prepared.2.request.source.b : ℝ))
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalAllowanceFresh.run fresh rich frame state).1.1.1.1.getD []) j : ℝ)) := by
  rw [BinaryTerminalPhysicalAllowanceFresh.run_data]
  exact BinaryPRGBooleanFreshLaw.every_path_fullBudget fresh frame prepared hRead rich state

theorem pair_every_path_fullBudget {S : Type*} (fresh : S → Bool × S)
    (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (state : S) :
    FullBudget (prepared.2.request.source.a : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalAllowanceFresh.pair fresh frame state).1.1.1.1.1.getD []) j : ℝ)) ∧
    FullBudget (prepared.2.request.source.b : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalAllowanceFresh.pair fresh frame state).1.1.1.1.2.getD []) j : ℝ)) := by
  rw [BinaryTerminalPhysicalAllowanceFresh.pair_data]
  exact BinaryPRGBooleanFreshLaw.pair_every_path_fullBudget fresh frame prepared hRead state

noncomputable def law (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) : Mixed prepared.1 :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (fun bits j => (allocation frame prepared rich bits j : ℝ))

theorem law_state (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) :
    law frame prepared rich = BinaryPRGBooleanFreshLaw.law frame prepared rich := by
  simp only [law,BinaryPRGBooleanFreshLaw.law,allocation_state]

def pairAllocation (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+
      sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    Allocation prepared.1 × Allocation prepared.1 :=
  let bytes := (BinaryTerminalPhysicalAllowanceFresh.pair
    (tapeFresh (vectorTape bits)) frame 0).1.1.1.1
  ((fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.1.getD []) j : ℝ)),
    (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.2.getD []) j : ℝ)))

theorem pairAllocation_state (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+
      sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    pairAllocation frame prepared bits =
      BinaryPRGBooleanFreshLaw.pairAllocation frame prepared bits := by
  simp only [pairAllocation,BinaryPRGBooleanFreshLaw.pairAllocation,
    BinaryTerminalPhysicalAllowanceFresh.pair_data]

noncomputable def pairLaw (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    ProbabilityMeasure (Allocation prepared.1 × Allocation prepared.1) :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision+
    sampleBitBudget prepared.1 prepared.2.request.precision)).map (pairAllocation frame prepared)

theorem pairLaw_state (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    pairLaw frame prepared = BinaryPRGBooleanFreshLaw.pairLaw frame prepared := by
  unfold pairLaw BinaryPRGBooleanFreshLaw.pairLaw
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
  exact BinaryPRGBooleanFreshLaw.pairLaw_product frame prepared hRead

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
  exact BinaryPRGBooleanFreshLaw.law_regrets frame prepared hRead

end Blotto.BinaryTerminalPhysicalAllowanceLaw
