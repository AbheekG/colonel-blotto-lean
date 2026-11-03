import Blotto.SequentialFairPRGSourceContracts
import Blotto.BinaryTerminalPhysicalParsedGeneratedLaw

/-! Whole allocation laws are interpreted from the actual fixed-source packet.
Original parser promises and continuous-game scopes are preserved. Source-model
cost/space bounds are kept separate from native compiler/runtime calibration. -/
namespace Blotto.SequentialFairPRGSourceLaw
open MeasureTheory RationalLottoResourceSystem FreshBitSeedLifetime
open BinarySeedPreparationSpace SequentialFairPRGSource FreshBitStateTransport
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] BinaryRawParserContinuation.generatedWithFactoryExtras BinaryRawParserContinuation.parsedGeneratedWithFactoryExtras BinaryRawParserContinuation.pairWithFactoryExtras BinaryRawParserContinuation.parsedPairWithFactoryExtras BinaryPromiseOpcodeRequest.generatedWithFactoryExtras BinaryPromiseOpcodeRequest.parsedGeneratedWithFactoryExtras BinaryPromiseOpcodeRequest.pairWithFactoryExtras BinaryPromiseOpcodeRequest.parsedPairWithFactoryExtras

theorem generated_vector_data {N : ℕ} (bits : Fin N → Bool) (rich : Bool) (frame : List Bool) :
    (generated rich frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.1 =
      (BinaryTerminalPhysicalCompleteGeneratedMeasured.run (tapeFresh (vectorTape bits)) rich frame 0).1.1.1.1 := by
  have h := congrArg (fun out => out.1.1.1.1.1.1.1.1.1.1.1) (generated_observables bits rich frame)
  simp only [mapState,mapLeft] at h
  exact h.trans (congrArg (fun out => out.1.1.1.1.1)
    (BinaryPromiseOpcodeRequest.generated_compat (tapeFresh (vectorTape bits)) rich frame 0))

theorem parsedGenerated_vector_data {N : ℕ} (bits : Fin N → Bool) (rich : Bool) (frame : List Bool) :
    (parsedGenerated rich frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.1 =
      (BinaryTerminalPhysicalParsedGeneratedMeasured.run (tapeFresh (vectorTape bits)) rich frame 0).1.1.1.1 := by
  have h := congrArg (fun out => out.1.1.1.1.1.1.1.1.1.1.1) (parsedGenerated_observables bits rich frame)
  simp only [mapState,mapLeft] at h
  exact h.trans (congrArg (fun out => out.1.1.1.1.1)
    (BinaryPromiseOpcodeRequest.parsedGenerated_compat (tapeFresh (vectorTape bits)) rich frame 0))

theorem pair_vector_data {N : ℕ} (bits : Fin N → Bool) (frame : List Bool) :
    (pair frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.1 =
      (BinaryTerminalPhysicalCompleteGeneratedMeasured.pair (tapeFresh (vectorTape bits)) frame 0).1.1.1.1 := by
  have h := congrArg (fun out => out.1.1.1.1.1.1.1.1.1.1.1) (pair_observables bits frame)
  simp only [mapState,mapLeft] at h
  exact h.trans (congrArg (fun out => out.1.1.1.1.1)
    (BinaryPromiseOpcodeRequest.pair_compat (tapeFresh (vectorTape bits)) frame 0))

theorem parsedPair_vector_data {N : ℕ} (bits : Fin N → Bool) (frame : List Bool) :
    (parsedPair frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.1 =
      (BinaryTerminalPhysicalParsedGeneratedMeasured.pair (tapeFresh (vectorTape bits)) frame 0).1.1.1.1 := by
  have h := congrArg (fun out => out.1.1.1.1.1.1.1.1.1.1.1) (parsedPair_observables bits frame)
  simp only [mapState,mapLeft] at h
  exact h.trans (congrArg (fun out => out.1.1.1.1.1)
    (BinaryPromiseOpcodeRequest.parsedPair_compat (tapeFresh (vectorTape bits)) frame 0))

def allocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) : Fin prepared.1 → ℚ :=
  BinaryPRGSeedOutputLaw.readback prepared.1
    ((parsedGenerated rich frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.1.getD [])

theorem allocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    allocation frame prepared rich bits = BinaryTerminalPhysicalParsedGeneratedLaw.allocation frame prepared rich bits := by
  simp only [allocation,BinaryTerminalPhysicalParsedGeneratedLaw.allocation,parsedGenerated_vector_data]

noncomputable def law (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) : Mixed prepared.1 :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (fun bits j => (allocation frame prepared rich bits j : ℝ))

theorem law_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool) :
    law frame prepared rich = BinaryTerminalPhysicalParsedGeneratedLaw.law frame prepared rich := by
  simp only [law,BinaryTerminalPhysicalParsedGeneratedLaw.law,allocation_state]

def pairAllocation (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    Allocation prepared.1 × Allocation prepared.1 :=
  let bytes := (parsedPair frame (List.ofFn bits)).1.1.1.1.1.1.1.1.1.1.1
  ((fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.1.getD []) j : ℝ)),
    (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1 (bytes.2.getD []) j : ℝ)))

theorem pairAllocation_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    pairAllocation frame prepared bits = BinaryTerminalPhysicalParsedGeneratedLaw.pairAllocation frame prepared bits := by
  simp only [pairAllocation,BinaryTerminalPhysicalParsedGeneratedLaw.pairAllocation,parsedPair_vector_data]

noncomputable def pairLaw (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    ProbabilityMeasure (Allocation prepared.1 × Allocation prepared.1) :=
  (fairBitLaw (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision)).map
    (pairAllocation frame prepared)

theorem pairLaw_state (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n) :
    pairLaw frame prepared = BinaryTerminalPhysicalParsedGeneratedLaw.pairLaw frame prepared := by
  unfold pairLaw BinaryTerminalPhysicalParsedGeneratedLaw.pairLaw
  congr 1
  funext bits
  exact pairAllocation_state frame prepared bits

theorem pairLaw_product (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    (pairLaw frame prepared : Measure (Allocation prepared.1 × Allocation prepared.1)) =
      (law frame prepared true : Measure (Allocation prepared.1)).prod (law frame prepared false : Measure (Allocation prepared.1)) := by
  rw [pairLaw_state,law_state,law_state]
  exact BinaryTerminalPhysicalParsedGeneratedLaw.pairLaw_product frame prepared hRead

theorem law_regrets (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) :
    regret prepared.2.request.source.realValues (prepared.2.request.source.a : ℝ)
      (law frame prepared true) (law frame prepared false) < prepared.2.request.accuracy.numeric.real ∧
    regret prepared.2.request.source.realValues (prepared.2.request.source.b : ℝ)
      (law frame prepared false) (law frame prepared true) < prepared.2.request.accuracy.numeric.real := by
  rw [law_state,law_state]
  exact BinaryTerminalPhysicalParsedGeneratedLaw.law_regrets frame prepared hRead

theorem drawCount_accepted (frame : List Bool)
    (prepared : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = some (prepared,[])) :
    drawCount frame = sampleBitBudget prepared.1 prepared.2.logical.request.precision := by
  have hPhys := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hRead
  have hBackend := (congrArg Prod.fst
    (BinaryRawParserContinuation.read_original BinaryPromiseOpcodeRequest.backend frame)).trans hPhys
  simp only [drawCount,hBackend,ite_true]

theorem allocation_fullBudget (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (rich : Bool) (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ) else (prepared.2.request.source.b : ℝ))
      (fun j => (allocation frame prepared rich bits j : ℝ)) := by
  rw [allocation_state]
  exact BinaryTerminalPhysicalParsedGeneratedLaw.every_path_fullBudget
    (tapeFresh (vectorTape bits)) frame prepared hRead rich 0

theorem pair_fullBudget (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    FullBudget (prepared.2.request.source.a : ℝ) (pairAllocation frame prepared bits).1 ∧
      FullBudget (prepared.2.request.source.b : ℝ) (pairAllocation frame prepared bits).2 := by
  rw [pairAllocation_state]
  exact BinaryTerminalPhysicalParsedGeneratedLaw.pair_every_path_fullBudget
    (tapeFresh (vectorTape bits)) frame prepared hRead 0

theorem accepted_pair_complete : ∃ C d : ℕ,∀ (prices : Representation) (frame : List Bool)
    (prepared : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestMeasured.read frame).1.1 = some (prepared,[]))
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.logical.request.precision+
      sampleBitBudget prepared.1 prepared.2.logical.request.precision) → Bool) (steps : ℕ),
    SequentialFairPRGSourceContracts.parsedPairCost frame (List.ofFn bits)+frame.length+(List.ofFn bits).length ≤
      C*(frame.length+1)^d ∧
    prices.listCellUnits*(frame.length+(List.ofFn bits).length)+
      representedWorkspace prices (parsedPair frame (List.ofFn bits)).1.1.1.1.1.1.1.1.2 steps ≤
      BinaryCompleteRepresentationSpace.units prices*(C*(frame.length+1)^d) ∧
    FullBudget (prepared.2.logical.request.source.a : ℝ)
      (pairAllocation frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) bits).1 ∧
    FullBudget (prepared.2.logical.request.source.b : ℝ)
      (pairAllocation frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) bits).2 ∧
    (pairLaw frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) :
      Measure (Allocation (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared).1 × Allocation (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared).1)) =
      (law frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) true : Measure (Allocation (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared).1)).prod
        (law frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) false : Measure (Allocation (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared).1)) ∧
    (regret prepared.2.logical.request.source.realValues (prepared.2.logical.request.source.a : ℝ)
      (law frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) true)
      (law frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) false) < prepared.2.logical.request.accuracy.numeric.real ∧
    regret prepared.2.logical.request.source.realValues (prepared.2.logical.request.source.b : ℝ)
      (law frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) false)
      (law frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) true) < prepared.2.logical.request.accuracy.numeric.real) := by
  obtain ⟨C,d,h⟩ := SequentialFairPRGSourceContracts.parsedPair_fair_complete
  refine ⟨C,d,?_⟩
  intro prices frame prepared hRead bits steps
  have hFrame := h prices frame
  rw [drawCount_accepted frame prepared hRead] at hFrame
  have hc := hFrame bits steps
  have hLogical := BinaryTerminalPhysicalParsedGeneratedLaw.accepted_logical frame prepared hRead
  have hb := pair_fullBudget frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) hLogical bits
  exact ⟨hc.1,hc.2,hb.1,hb.2,
    pairLaw_product frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) hLogical,
    law_regrets frame (BinaryTerminalPhysicalParsedGeneratedLaw.logical prepared) hLogical⟩

end Blotto.SequentialFairPRGSourceLaw
