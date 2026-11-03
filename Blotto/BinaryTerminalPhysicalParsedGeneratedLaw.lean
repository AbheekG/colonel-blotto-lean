import Blotto.BinaryTerminalPhysicalParsedGeneratedMeasured
import Blotto.BinaryTerminalPhysicalCompleteGeneratedLaw

/-! Laws are defined from the actual parser-priced generated producers.
Exact old full-data/trace erasure preserves fair-bit kernels, hard budgets
on every path, independent whole-allocation pair laws and strict continuous
regrets. Accepted actual physical parser output supplies the logical premise. -/
namespace Blotto.BinaryTerminalPhysicalParsedGeneratedLaw
open MeasureTheory RationalLottoResourceSystem FreshBitSeedLifetime
set_option autoImplicit false

def logical (prepared : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) :
    Σ n,BinaryPRGAccuracyRulerRequest.Request n := ⟨prepared.1,prepared.2.logical⟩

theorem accepted_logical (frame : List Bool) (prepared : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = some (prepared,[])) :
    (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (logical prepared,[]) := by
  have h := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hRead
  rw [hOld,Option.map_some] at h
  simpa only [BinaryPRGPhysicalRawRequestLifetime.forgetParsed,logical] using h.symm

theorem kernel_operational (rich : Bool) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.kernel rich frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryTerminalPhysicalParsedGeneratedMeasured.run
          (tapeFresh (vectorTape bits)) rich frame 0).1.1.1.1) := by
  simpa only [BinaryTerminalPhysicalParsedGeneratedMeasured.run_erases] using
    BinaryTerminalPhysicalCompleteGeneratedLaw.kernel_operational rich frame prepared hRead f

theorem pairKernel_operational (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) × Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.pairKernel frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision+
        sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (BinaryTerminalPhysicalParsedGeneratedMeasured.pair
          (tapeFresh (vectorTape bits)) frame 0).1.1.1.1) := by
  simpa only [BinaryTerminalPhysicalParsedGeneratedMeasured.pair_erases] using
    BinaryTerminalPhysicalCompleteGeneratedLaw.pairKernel_operational frame prepared hRead f

def allocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) : Fin prepared.1 → ℚ :=
  BinaryPRGSeedOutputLaw.readback prepared.1
    ((BinaryTerminalPhysicalParsedGeneratedMeasured.run
      (tapeFresh (vectorTape bits)) rich frame 0).1.1.1.1.getD [])

theorem allocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    allocation frame prepared rich bits = BinaryTerminalPhysicalCompleteGeneratedLaw.allocation frame prepared rich bits := by
  simp only [allocation,BinaryTerminalPhysicalCompleteGeneratedLaw.allocation,
    BinaryTerminalPhysicalParsedGeneratedMeasured.run_erases]

theorem every_path_fullBudget {S : Type*} (fresh : S → Bool × S) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (rich : Bool) (state : S) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ) else (prepared.2.request.source.b : ℝ))
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalParsedGeneratedMeasured.run fresh rich frame state).1.1.1.1.getD []) j : ℝ)) := by
  rw [BinaryTerminalPhysicalParsedGeneratedMeasured.run_erases]
  exact BinaryTerminalPhysicalCompleteGeneratedLaw.every_path_fullBudget fresh frame prepared hRead rich state

theorem pair_every_path_fullBudget {S : Type*} (fresh : S → Bool × S) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (state : S) :
    FullBudget (prepared.2.request.source.a : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalParsedGeneratedMeasured.pair fresh frame state).1.1.1.1.1.getD []) j : ℝ)) ∧
    FullBudget (prepared.2.request.source.b : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((BinaryTerminalPhysicalParsedGeneratedMeasured.pair fresh frame state).1.1.1.1.2.getD []) j : ℝ)) := by
  rw [BinaryTerminalPhysicalParsedGeneratedMeasured.pair_erases]
  exact BinaryTerminalPhysicalCompleteGeneratedLaw.pair_every_path_fullBudget fresh frame prepared hRead state

noncomputable def law (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) : Mixed prepared.1 :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (fun bits j => (allocation frame prepared rich bits j : ℝ))

theorem law_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) :
    law frame prepared rich = BinaryTerminalPhysicalCompleteGeneratedLaw.law frame prepared rich := by
  simp only [law,BinaryTerminalPhysicalCompleteGeneratedLaw.law,allocation_state]

def pairAllocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+
      sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) : Allocation prepared.1 × Allocation prepared.1 :=
  let bytes := (BinaryTerminalPhysicalParsedGeneratedMeasured.pair
    (tapeFresh (vectorTape bits)) frame 0).1.1.1.1
  ((fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.1.getD []) j : ℝ)),
    (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.2.getD []) j : ℝ)))

theorem pairAllocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+
      sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    pairAllocation frame prepared bits = BinaryTerminalPhysicalCompleteGeneratedLaw.pairAllocation frame prepared bits := by
  simp only [pairAllocation,BinaryTerminalPhysicalCompleteGeneratedLaw.pairAllocation,
    BinaryTerminalPhysicalParsedGeneratedMeasured.pair_erases]

noncomputable def pairLaw (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    ProbabilityMeasure (Allocation prepared.1 × Allocation prepared.1) :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision+
    sampleBitBudget prepared.1 prepared.2.request.precision)).map (pairAllocation frame prepared)

theorem pairLaw_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    pairLaw frame prepared = BinaryTerminalPhysicalCompleteGeneratedLaw.pairLaw frame prepared := by
  unfold pairLaw BinaryTerminalPhysicalCompleteGeneratedLaw.pairLaw
  congr 1
  funext bits
  exact pairAllocation_state frame prepared bits

theorem pairLaw_product (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    (pairLaw frame prepared : Measure (Allocation prepared.1 × Allocation prepared.1)) =
      (law frame prepared true : Measure (Allocation prepared.1)).prod
        (law frame prepared false : Measure (Allocation prepared.1)) := by
  rw [pairLaw_state,law_state,law_state]
  exact BinaryTerminalPhysicalCompleteGeneratedLaw.pairLaw_product frame prepared hRead

theorem law_regrets (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    regret prepared.2.request.source.realValues (prepared.2.request.source.a : ℝ)
      (law frame prepared true) (law frame prepared false) < prepared.2.request.accuracy.numeric.real ∧
    regret prepared.2.request.source.realValues (prepared.2.request.source.b : ℝ)
      (law frame prepared false) (law frame prepared true) < prepared.2.request.accuracy.numeric.real := by
  rw [law_state,law_state]
  exact BinaryTerminalPhysicalCompleteGeneratedLaw.law_regrets frame prepared hRead

end Blotto.BinaryTerminalPhysicalParsedGeneratedLaw
