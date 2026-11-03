import Blotto.BinaryReachedTerminal
import Blotto.WordRestrictedIndexedRefinement
import Blotto.NativeBinaryNestedSampler

/-! The exact Boolean resource result is transported to the original retained
capacity function and invariant-restricted phase, preserving the shared reader
position and both successful/failed results. Terminal certificates and profile
nonnegativity are derived in Prop from the actual six-word setup/run. No source
state, resource invariant or terminal descriptor factory is supplied at runtime. -/
namespace Blotto.BinaryReflectedPhaseRefinement
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinaryThreeResourcePair BinarySharedResourceRun

-- Equality of capacities changes only the proof index of the retained state.
def transportState {n : ℕ} {L L' : Fin n → ℚ} (he : L=L') (state : RationalActiveResources L) :
    RationalActiveResources L' := he ▸ state

theorem transportState_resource {n : ℕ} {L L' : Fin n → ℚ} (he : L=L') (state : RationalActiveResources L) :
    (transportState he state).resource=state.resource := by cases he; rfl

theorem transportState_active {n : ℕ} {L L' : Fin n → ℚ} (he : L=L') (state : RationalActiveResources L) :
    (transportState he state).active=state.active := by cases he; rfl

theorem transportState_initial {n : ℕ} {L L' : Fin n → ℚ} (he : L=L') (r : Fin n → ℚ) :
    transportState he (RationalActiveResources.initial L r)=RationalActiveResources.initial L' r := by cases he; rfl

theorem active_eq_of_data {n : ℕ} {L : Fin n → ℚ} (s t : RationalActiveResources L)
    (hResource : s.resource=t.resource) (hActive : s.active=t.active) : s=t := by
  cases s
  cases t
  cases hResource
  cases hActive
  rfl

def transportResult {n : ℕ} {L L' : Fin n → ℚ} (he : L=L')
    (result : Option (RationalActiveResources L) × ℕ) : Option (RationalActiveResources L') × ℕ :=
  (result.1.map (transportState he),result.2)

theorem resource_run_transport {n : ℕ} {L L' : Fin n → ℚ} (he : L=L')
    (N : ℕ) (state : RationalActiveResources L) (bits : Fin N → Bool) :
    transportResult he ((rationalResourceMachine L).run N (.ready state) bits) =
      (rationalResourceMachine L').run N (.ready (transportState he state)) bits := by
  cases he
  change (((rationalResourceMachine L).run N (.ready state) bits).1.map id,
    ((rationalResourceMachine L).run N (.ready state) bits).2) =
      (rationalResourceMachine L).run N (.ready state) bits
  rw [Option.map_id]
  rfl


theorem capacity_eq (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell) :
    (fun j => value ((prepare input).capacity.read j))=(source.reflectedResourceSystem hCase).capacity := by
  funext j
  exact capacity_value _ _ (prepare_canonical input hC) (prepare_refines input source hC hr hCase) j

theorem sourceState_transport (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (result : Certified (prepare input).capacity) :
    BinaryReachedTerminal.sourceState input source hC hr hCase result =
      transportState (capacity_eq input source hC hr hCase) result.reference := by
  apply active_eq_of_data
  · rw [transportState_resource]
    rfl
  · rw [transportState_active]
    rfl

theorem setupState_transport (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell) :
    transportState (capacity_eq input source hC hr hCase) (setupState input hC).reference =
      (source.reflectedResourceSystem hCase).initialState := by
  rw [setupState,initial_reference,transportState_initial]
  have hi : (fun j => value ((prepare input).initial.read j))=(source.reflectedResourceSystem hCase).initial := by
    funext j
    exact (prepare_refines input source hC hr hCase).2.2.2 j
  rw [hi]
  rfl

noncomputable def sourceMapResult (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (result : Option (Certified (prepare input).capacity) × ℕ) :
    Option (RationalActiveResources (source.reflectedResourceSystem hCase).capacity) × ℕ :=
  (result.1.map (BinaryReachedTerminal.sourceState input source hC hr hCase),result.2)

theorem sourceMapResult_transport (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (result : Option (Certified (prepare input).capacity) × ℕ) :
    sourceMapResult input source hC hr hCase result =
      transportResult (capacity_eq input source hC hr hCase) (mapResult result) := by
  rcases result with ⟨option,pos⟩
  cases option with
  | none => rfl
  | some result =>
    change (some (BinaryReachedTerminal.sourceState input source hC hr hCase result),pos)=
      (some (transportState (capacity_eq input source hC hr hCase) result.reference),pos)
    rw [sourceState_transport]

theorem setupRun_source_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) :
    sourceMapResult input source hC hr hCase (setupRun input hC N bits) =
      (rationalResourceMachine (source.reflectedResourceSystem hCase).capacity).run N
        (.ready (source.reflectedResourceSystem hCase).initialState) bits := by
  rw [sourceMapResult_transport]
  have he := run_refines (capacity_canonical _ (prepare_canonical input hC)) N (setupState input hC) bits
  change mapResult (setupRun input hC N bits)=_ at he
  rw [he,resource_run_transport,setupState_transport input source hC hr hCase]

theorem setupRun_phase_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) :
    sourceMapResult input source hC hr hCase (setupRun input hC N bits) =
      WordRestrictedIndexedRefinement.eraseResult (source.reflectedResourceSystem hCase).TerminalState
        ((source.reflectedResourceSystem hCase).phase.run N (source.reflectedResourceSystem hCase).start bits) := by
  have he := WordRestrictedIndexedRefinement.run_refines
    (rationalResourceMachine (source.reflectedResourceSystem hCase).capacity)
    (source.reflectedResourceSystem hCase).CursorInvariant (source.reflectedResourceSystem hCase).TerminalState
    (source.reflectedResourceSystem hCase).phaseProof N bits (source.reflectedResourceSystem hCase).start
  exact (setupRun_source_refines input source hC hr hCase N bits).trans he.symm

theorem setupRun_phase_indexed_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) :
    sourceMapResult input source hC hr hCase (setupRun input hC N bits) =
      WordRestrictedIndexedRefinement.eraseResult (source.reflectedResourceSystem hCase).TerminalState
        ((source.reflectedResourceSystem hCase).phase.runCursorIndexed N bits
          (.state (source.reflectedResourceSystem hCase).start) 0 (Nat.zero_le N)) := by
  have he := setupRun_phase_refines input source hC hr hCase N bits
  rw [WordStateMachine.run_eq_numeric] at he
  exact he

theorem setupRun_phase_failure_iff (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) :
    (setupRun input hC N bits).1=none ↔
      ((source.reflectedResourceSystem hCase).phase.run N (source.reflectedResourceSystem hCase).start bits).1=none := by
  have he := congrArg Prod.fst (setupRun_phase_refines input source hC hr hCase N bits)
  change (setupRun input hC N bits).1.map (BinaryReachedTerminal.sourceState input source hC hr hCase)=
    (((source.reflectedResourceSystem hCase).phase.run N (source.reflectedResourceSystem hCase).start bits).1.map Subtype.val) at he
  have hn := congrArg (fun option => option=none) he
  simpa only [Option.map_eq_none_iff] using Iff.of_eq hn

noncomputable def phaseResult (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1=some result) : (source.reflectedResourceSystem hCase).PhaseResult :=
  ⟨BinaryReachedTerminal.sourceState input source hC hr hCase result,
    BinaryReachedTerminal.sourceState_invariant input source hC hr hCase N bits result hSuccess,
    (setupRun_terminal_contract input source hC hr hCase N bits result hSuccess).1⟩

theorem setupRun_phase_success (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1=some result) :
    ((source.reflectedResourceSystem hCase).phase.run N (source.reflectedResourceSystem hCase).start bits).1 =
      some (phaseResult input source hC hr hCase N bits result hSuccess) := by
  have he := congrArg Prod.fst (setupRun_phase_refines input source hC hr hCase N bits)
  change (setupRun input hC N bits).1.map (BinaryReachedTerminal.sourceState input source hC hr hCase)=
    (((source.reflectedResourceSystem hCase).phase.run N (source.reflectedResourceSystem hCase).start bits).1.map Subtype.val) at he
  rw [hSuccess,Option.map_some] at he
  cases hp : ((source.reflectedResourceSystem hCase).phase.run N (source.reflectedResourceSystem hCase).start bits).1 with
  | none => rw [hp,Option.map_none] at he; cases he
  | some value =>
    rw [hp,Option.map_some] at he
    have hv : value=phaseResult input source hC hr hCase N bits result hSuccess := by
      apply Subtype.ext
      exact (Option.some.inj he).symm
    rw [hv]

theorem setupRun_phase_position (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) :
    (setupRun input hC N bits).2=
      ((source.reflectedResourceSystem hCase).phase.run N (source.reflectedResourceSystem hCase).start bits).2 :=
  congrArg Prod.snd (setupRun_phase_refines input source hC hr hCase N bits)

theorem terminal_eq_phaseData (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1=some result) :
    BinaryReachedTerminal.terminal input source hC hr hCase N bits result hSuccess =
      (source.reflectedResourceSystem hCase).terminalData
        (phaseResult input source hC hr hCase N bits result hSuccess) := rfl

theorem terminal_profile_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1=some result) (K : ℕ) (outer : Fin K → Bool) :
    (BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer).Refines
      (((source.reflectedResourceSystem hCase).terminalData
        (phaseResult input source hC hr hCase N bits result hSuccess)).profile K outer) :=
  BinaryReachedTerminal.profile_refines input source hC hr hCase N bits result hSuccess K outer

theorem terminal_input_admissible (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1=some result) :
    NativeBinaryNestedSampler.Admissible (BinaryNestedTerminalInput.prepare (prepare input) result.state) :=
  ⟨(BinaryReachedTerminal.terminal input source hC hr hCase N bits result hSuccess).input,
    BinaryNestedTerminalInput.prepare_refines _ _ _ (prepare_canonical input hC) result.canonical
      (BinaryReachedTerminal.terminal_data_refines input source hC hr hCase N bits result hSuccess)⟩

theorem terminal_profile_nonnegative (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w<(1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1=some result) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot, 0 ≤ value ((BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer).weight.read slot) := by
  intro slot
  rw [(terminal_profile_refines input source hC hr hCase N bits result hSuccess K outer).1 slot]
  exact (((source.reflectedResourceSystem hCase).terminalData
    (phaseResult input source hC hr hCase N bits result hSuccess)).profile K outer).nonnegative slot

end Blotto.BinaryReflectedPhaseRefinement
