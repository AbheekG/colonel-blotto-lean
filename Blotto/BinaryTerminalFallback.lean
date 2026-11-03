import Blotto.BinaryResourceFallback
import Blotto.BinaryCategoricalFallback
import Blotto.BinaryReflectedTerminalEmission
import Blotto.BinaryReachedTerminal
import Blotto.BinaryReflectedPhaseRefinement
import Blotto.WordMachineLowerLeaf

/-! The deterministic fallback rebuilds the actual terminal profile after the
native lower resource path, follows the categorical lower leaf, interpolates
one selected slot, then reflects to the original four coordinates. A source
existence witness is Prop-only and supplies erased validity proofs, never data. -/

namespace Blotto.BinaryTerminalFallback
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinaryThreeResourcePair BinaryNestedTerminalInput
open scoped BigOperators

def Admissible (input : BinaryFourParameters.Input) : Prop:=
  ∃ source : RationalFourInput, input.Refines source ∧ source.w < (1-source.p)*source.ell

noncomputable def sourceState (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) :
    RationalActiveResources (source.reflectedResourceSystem hCase).capacity:=
  BinaryReachedTerminal.sourceState input source hC hr hCase (BinaryResourceFallback.setup input hC)

theorem sourceState_invariant (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) :
    RationalResourceInvariant (source.reflectedResourceSystem hCase).capacity
      ((source.reflectedResourceSystem hCase).totalResource : ℝ) (sourceState input source hC hr hCase):=by
  have ht:=BinaryResourceFallback.setup_terminal_contract input source hC hr hCase
  have hCap:=capacity_value (prepare input) (source.reflectedResourceSystem hCase) (prepare_canonical input hC)
    (prepare_refines input source hC hr hCase)
  have hRow : (sourceState input source hC hr hCase).resource.realAllocation=
      fun j=>(value ((BinaryResourceFallback.setup input hC).state.resource.read j) : ℝ):=by
    funext j
    exact congrArg (fun q : ℚ=>(q : ℝ))
      (BinaryReachedTerminal.sourceState_allocation input source hC hr hCase (BinaryResourceFallback.setup input hC) j)
  unfold RationalResourceInvariant
  rw [hRow]
  refine ⟨?_,ht.2.2⟩
  intro j
  have hb:=ht.2.1 j
  dsimp only at hb ⊢
  rw [hCap j] at hb
  exact hb

noncomputable def terminal (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) : RationalTerminalResources:=
  (source.reflectedResourceSystem hCase).terminal (sourceState input source hC hr hCase)
    (sourceState_invariant input source hC hr hCase)
    (BinaryResourceFallback.setup_terminal_contract input source hC hr hCase).1

theorem terminal_data_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) :
    DataRefines (prepare input) (BinaryResourceFallback.setup input hC).state (terminal input source hC hr hCase):=
  BinaryNestedTerminalInput.terminal_data_refines _ _ _ _ _ _ (prepare_refines input source hC hr hCase)
    (fun j=>(BinaryReachedTerminal.sourceState_allocation input source hC hr hCase (BinaryResourceFallback.setup input hC) j).symm)

def table (input : BinaryFourParameters.Input) (hC : input.Canonical) (K : ℕ) (outer : Fin K→Bool) :
    BinaryStoredOverlapEnvironment.Segment 3 18:=
  BinaryTerminalProfileCompiler.profile (prepare input) (BinaryResourceFallback.setup input hC).state K outer

theorem table_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (K : ℕ) (outer : Fin K→Bool) :
    (table input hC K outer).Canonical:=
  BinaryTerminalProfileCompiler.profile_canonical _ _ (prepare_canonical input hC)
    (BinaryResourceFallback.setup input hC).canonical K outer

theorem table_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (K : ℕ) (outer : Fin K→Bool) :
    (table input hC K outer).Refines ((terminal input source hC hr hCase).profile K outer):=
  BinaryTerminalProfileCompiler.profile_refines _ _ _ (prepare_canonical input hC)
    (BinaryResourceFallback.setup input hC).canonical (terminal_data_refines input source hC hr hCase) K outer

theorem table_nonnegative (input : BinaryFourParameters.Input) (hC : input.Canonical) (ha : Admissible input)
    (K : ℕ) (outer : Fin K→Bool) : ∀ i,0≤value ((table input hC K outer).weight.read i):=by
  obtain ⟨source,hr,hCase⟩:=ha
  intro i
  rw [(table_refines input source hC hr hCase K outer).1 i]
  exact ((terminal input source hC hr hCase).profile K outer).nonnegative i

def slot (input : BinaryFourParameters.Input) (hC : input.Canonical) (ha : Admissible input)
    (K : ℕ) (outer : Fin K→Bool) : Fin 18:=
  BinaryCategoricalFallback.segment (table input hC K outer) (table_canonical input hC K outer)
    (table_nonnegative input hC ha K outer) 0

def sample (input : BinaryFourParameters.Input) (hC : input.Canonical) (ha : Admissible input)
    (K : ℕ) (outer scalar : Fin K→Bool) : FixedArrayTable 4 SignedWord:=
  BinaryReflectedTerminalEmission.sample input (BinaryResourceFallback.setup input hC).state K outer scalar
    (slot input hC ha K outer)

theorem slot_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (ha : Admissible input) (hr : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (K : ℕ) (outer : Fin K→Bool) :
    slot input hC ha K outer=(categoricalMachine (0 : Fin 18)).chooseLeaf ((terminal input source hC hr hCase).profile K outer).start:=
  BinaryCategoricalFallback.segment_refines _ _ (table_canonical input hC K outer) _
    (table_refines input source hC hr hCase K outer) 0

theorem sample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (ha : Admissible input)
    (K : ℕ) (outer scalar : Fin K→Bool) : ∀ j,CanonicalWord ((sample input hC ha K outer scalar).read j):=
  BinaryReflectedTerminalEmission.sample_canonical input _ hC (BinaryResourceFallback.setup input hC).canonical K outer scalar _

theorem sample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (ha : Admissible input) (hr : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (K : ℕ) (outer scalar : Fin K→Bool) :
    FullBudget (source.B : ℝ) (fun j=>(value ((sample input hC ha K outer scalar).read j) : ℝ)):=
  BinaryReflectedTerminalEmission.sample_fullBudget input source _ _ hC hr hCase
    (BinaryResourceFallback.setup input hC).canonical (terminal_data_refines input source hC hr hCase) K outer scalar _

theorem sample_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (ha : Admissible input) (hr : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (K : ℕ) (outer scalar : Fin K→Bool) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j=>(value ((sample input hC ha K outer scalar).read j) : ℝ)):=
  BinaryReflectedTerminalEmission.sample_inBox input source _ _ hC hr
    (BinaryResourceFallback.setup input hC).canonical (terminal_data_refines input source hC hr hCase) K outer scalar _


theorem resource_choose_transport {n : ℕ} {L L' : Fin n→ℚ} (he : L=L') (state : RationalActiveResources L) :
    BinaryReflectedPhaseRefinement.transportState he ((rationalResourceMachine L).chooseLeaf (.ready state))=
      (rationalResourceMachine L').chooseLeaf (.ready (BinaryReflectedPhaseRefinement.transportState he state)):=by
  cases he
  rfl

theorem sourceState_eq_phase_leaf (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) :
    sourceState input source hC hr hCase=
      (((source.reflectedResourceSystem hCase).phase).chooseLeaf ((source.reflectedResourceSystem hCase).start)).1:=by
  unfold sourceState
  rw [BinaryReflectedPhaseRefinement.sourceState_transport]
  have he:=BinaryResourceFallback.choose_refines
    (capacity_canonical _ (prepare_canonical input hC)) (BinarySharedResourceRun.setupState input hC)
  change (BinaryResourceFallback.setup input hC).reference=_ at he
  rw [he,resource_choose_transport,BinaryReflectedPhaseRefinement.setupState_transport input source hC hr hCase]
  exact ((rationalResourceMachine (source.reflectedResourceSystem hCase).capacity).restricted_chooseLeaf
    (source.reflectedResourceSystem hCase).CursorInvariant (source.reflectedResourceSystem hCase).TerminalState
    (source.reflectedResourceSystem hCase).phaseProof (source.reflectedResourceSystem hCase).start).symm

theorem terminal_eq_phase_leaf (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) :
    terminal input source hC hr hCase=
      (source.reflectedResourceSystem hCase).terminalData
        ((source.reflectedResourceSystem hCase).phase.chooseLeaf (source.reflectedResourceSystem hCase).start):=by
  unfold terminal RationalNestedResourceSystem.terminalData
  congr 1
  exact sourceState_eq_phase_leaf input source hC hr hCase

theorem sample_value (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (ha : Admissible input) (hr : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (K : ℕ) (outer scalar : Fin K→Bool) (j : Fin 4) :
    value ((sample input hC ha K outer scalar).read j)=
      (RationalAffineAllocation.reflectAppend source.originalLengths).value
        ((source.reflectedResourceSystem hCase).fallback K outer scalar) j:=by
  have he:=BinaryReflectedTerminalEmission.sample_value input source (BinaryResourceFallback.setup input hC).state
    (terminal input source hC hr hCase) hC hr (BinaryResourceFallback.setup input hC).canonical
    (terminal_data_refines input source hC hr hCase) K outer scalar (slot input hC ha K outer) j
  change value ((sample input hC ha K outer scalar).read j)=_ at he
  rw [slot_refines input source hC ha hr hCase K outer] at he
  rw [terminal_eq_phase_leaf input source hC hr hCase] at he
  rw [RationalNestedResourceSystem.fallback,RationalNestedResourceSystem.machine,
    RationalNestedResourceSystem.samplingStart,WordStateMachine.serial_chooseLeaf,
    RationalNestedResourceSystem.continuationMachine,RationalNestedResourceSystem.continuationStart,
    RationalSegmentLottery.machine,WordStateMachine.mapped_chooseLeaf]
  exact he

end Blotto.BinaryTerminalFallback
