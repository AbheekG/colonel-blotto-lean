import Blotto.BinaryGeneralResourceRun
import Blotto.BinaryTerminalGrouping
import Blotto.RationalLottoResourceSystem
import Blotto.WordRestrictedIndexedRefinement
import Blotto.WordMachineLowerLeaf

/-! Stored arbitrary-dimensional Lotto input executes native resource rounding.
An existential valid-source witness is Prop-only. Initial box/total 2B are
derived from that source, and successful native results prepare actual terminal
grouping fields. Semantic capacity transport and ofActive occur only in proofs.
No source/factory is a runtime argument. -/

namespace Blotto.BinaryLottoResourceInput
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourcePair
open scoped BigOperators

structure Input (n : ℕ) where
  budget : SignedWord
  length : FixedArrayTable n SignedWord
  resource : FixedArrayTable n SignedWord

def Input.Canonical {n : ℕ} (input : Input n) : Prop:=CanonicalWord input.budget ∧
  (∀ j,CanonicalWord (input.length.read j)) ∧ (∀ j,CanonicalWord (input.resource.read j))

def Input.Refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n) : Prop:=
  value input.budget=source.B ∧ (∀ j,value (input.length.read j)=source.length j) ∧
  (∀ j,value (input.resource.read j)=source.initial j)

def Admissible {n : ℕ} (input : Input n) : Prop:=∃ source : RationalLottoResourceSystem n,input.Refines source

def initial {n : ℕ} (input : Input n) (hC : input.Canonical) : Certified input.length:=
  BinaryResourcePair.initial input.length input.resource hC.2.1 hC.2.2

def run {n : ℕ} (input : Input n) (hC : input.Canonical) (N : ℕ) (bits : Fin N→Bool) : Option (Certified input.length)×ℕ:=
  BinaryGeneralResourceRun.run hC.2.1 N (initial input hC) bits

def groupingInput {n : ℕ} (input : Input n) (state : Certified input.length) : BinaryTerminalGrouping.Input n:=
  ⟨input.budget,input.length,state.state.resource⟩

theorem groupingInput_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) (state : Certified input.length) :
    (groupingInput input state).Canonical:=⟨hC.1,hC.2.1,state.canonical⟩

theorem initial_invariant {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) :
    RationalResourceInvariant (fun j=>value (input.length.read j)) (2*(source.B : ℝ)) (initial input hC).reference:=by
  rw [initial,BinaryResourcePair.initial_reference]
  unfold RationalResourceInvariant
  rw [RationalActiveResources.initial,RationalResourceArray.realAllocation_ofAllocation]
  constructor
  · intro j
    change (0 : ℝ)≤(value (input.resource.read j) : ℝ) ∧
      (value (input.resource.read j) : ℝ)≤(value (input.length.read j) : ℝ)
    rw [hr.2.2 j,hr.2.1 j]
    exact_mod_cast source.initial_box j
  · have he:=source.initial_sum
    have hi : (fun j=>(value (input.resource.read j) : ℝ))=fun j=>(source.initial j : ℝ):=by
      funext j
      rw [hr.2.2 j]
    rw [hi]
    exact_mod_cast he

theorem initial_invariant_native {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input) :
    RationalResourceInvariant (fun j=>value (input.length.read j)) (2*(value input.budget : ℝ)) (initial input hC).reference:=by
  obtain ⟨source,hr⟩:=hAd
  rw [hr.1]
  exact initial_invariant input source hC hr

noncomputable def sourceState {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) (state : Certified input.length) : RationalActiveResources source.length where
  resource:=RationalResourceArray.ofAllocation (fun j=>value (state.state.resource.read j))
  active:=state.state.active
  nodup:=state.nodup
  membership:=by
    intro j
    rw [RationalResourceArray.allocation_ofAllocation,←hr.2.1 j]
    exact state.membership j

theorem sourceState_allocation {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) (state : Certified input.length) (j : Fin n) :
    (sourceState input source hr state).resource.allocation j=value (state.state.resource.read j):=
  congrFun (RationalResourceArray.allocation_ofAllocation _) j

theorem sourceState_invariant {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) (state : Certified input.length)
    (hs : RationalResourceInvariant (fun j=>value (input.length.read j)) (2*(source.B : ℝ)) state.reference) :
    RationalResourceInvariant source.length (2*(source.B : ℝ)) (sourceState input source hr state):=by
  have hRow : (sourceState input source hr state).resource.realAllocation=state.reference.resource.realAllocation:=by
    funext j
    simp only [sourceState,Certified.reference,RationalResourceArray.realAllocation,
      RationalResourceArray.allocation_ofAllocation,BinaryResourceState.allocation]
  unfold RationalResourceInvariant
  rw [hRow]
  refine ⟨?_,hs.2⟩
  intro j
  have hb:=hs.1 j
  dsimp only at hb ⊢
  rw [hr.2.1 j] at hb
  exact hb

noncomputable def terminalOf {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) (state : Certified input.length)
    (hs : RationalResourceInvariant (fun j=>value (input.length.read j)) (2*(source.B : ℝ)) state.reference)
    (ht : state.state.active.length≤1) : RationalTerminalLotto n:=
  RationalTerminalLotto.ofActive source.B source.length source.B_pos source.length_pos source.length_le
    (sourceState input source hr state) (sourceState_invariant input source hr state hs) ht

theorem groupingInput_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) (state : Certified input.length)
    (hs : RationalResourceInvariant (fun j=>value (input.length.read j)) (2*(source.B : ℝ)) state.reference)
    (ht : state.state.active.length≤1) :
    (groupingInput input state).Refines (terminalOf input source hr state hs ht):=
  ⟨hr.1,hr.2.1,fun j=>(sourceState_allocation input source hr state j).symm⟩

theorem run_invariant {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) (result : Certified input.length)
    (hSuccess : (run input hC N bits).1=some result) :
    RationalResourceInvariant (fun j=>value (input.length.read j)) (2*(source.B : ℝ)) result.reference:=
  BinaryGeneralResourceRun.run_invariant hC.2.1 _ N (initial input hC) result bits
    (initial_invariant input source hC hr) hSuccess

theorem run_terminal {n : ℕ} (input : Input n) (hC : input.Canonical) (N : ℕ) (bits : Fin N→Bool)
    (result : Certified input.length) (hSuccess : (run input hC N bits).1=some result) : result.state.active.length≤1:=
  BinaryGeneralResourceRun.run_terminal hC.2.1 N (initial input hC) result bits hSuccess

noncomputable def reachedTerminal {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) (result : Certified input.length)
    (hSuccess : (run input hC N bits).1=some result) : RationalTerminalLotto n:=
  terminalOf input source hr result (run_invariant input source hC hr N bits result hSuccess)
    (run_terminal input hC N bits result hSuccess)

theorem reachedGrouping_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) (result : Certified input.length)
    (hSuccess : (run input hC N bits).1=some result) :
    (groupingInput input result).Refines (reachedTerminal input source hC hr N bits result hSuccess):=
  groupingInput_refines input source hr result _ _


def transportState {n : ℕ} {L L' : Fin n→ℚ} (he : L=L') (state : RationalActiveResources L) : RationalActiveResources L':=he ▸ state

theorem transportState_resource {n : ℕ} {L L' : Fin n→ℚ} (he : L=L') (state : RationalActiveResources L) :
    (transportState he state).resource=state.resource:=by cases he; rfl

theorem transportState_active {n : ℕ} {L L' : Fin n→ℚ} (he : L=L') (state : RationalActiveResources L) :
    (transportState he state).active=state.active:=by cases he; rfl

theorem transportState_initial {n : ℕ} {L L' : Fin n→ℚ} (he : L=L') (r : Fin n→ℚ) :
    transportState he (RationalActiveResources.initial L r)=RationalActiveResources.initial L' r:=by cases he; rfl

theorem active_eq_of_data {n : ℕ} {L : Fin n→ℚ} (first second : RationalActiveResources L)
    (hResource : first.resource=second.resource) (hActive : first.active=second.active) : first=second:=by
  cases first
  cases second
  cases hResource
  cases hActive
  rfl

theorem capacity_eq {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n) (hr : input.Refines source) :
    (fun j=>value (input.length.read j))=source.length:=funext hr.2.1

theorem sourceState_transport {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) (state : Certified input.length) :
    sourceState input source hr state=transportState (capacity_eq input source hr) state.reference:=by
  apply active_eq_of_data
  · rw [transportState_resource]
    rfl
  · rw [transportState_active]
    rfl

theorem initial_transport {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) :
    transportState (capacity_eq input source hr) (initial input hC).reference=source.initialState:=by
  rw [initial,BinaryResourcePair.initial_reference,transportState_initial]
  rw [show (fun j=>value (input.resource.read j))=source.initial from funext hr.2.2]
  rfl

def transportResult {n : ℕ} {L L' : Fin n→ℚ} (he : L=L')
    (result : Option (RationalActiveResources L)×ℕ) : Option (RationalActiveResources L')×ℕ:=
  (result.1.map (transportState he),result.2)

theorem resource_run_transport {n : ℕ} {L L' : Fin n→ℚ} (he : L=L') (N : ℕ)
    (state : RationalActiveResources L) (bits : Fin N→Bool) :
    transportResult he ((rationalResourceMachine L).run N (.ready state) bits)=
      (rationalResourceMachine L').run N (.ready (transportState he state)) bits:=by
  cases he
  change (((rationalResourceMachine L).run N (.ready state) bits).1.map id,
    ((rationalResourceMachine L).run N (.ready state) bits).2)=_
  rw [Option.map_id]
  rfl

noncomputable def sourceResult {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) (result : Option (Certified input.length)×ℕ) :
    Option (RationalActiveResources source.length)×ℕ:=
  (result.1.map (sourceState input source hr),result.2)

theorem sourceResult_transport {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) (result : Option (Certified input.length)×ℕ) :
    sourceResult input source hr result=transportResult (capacity_eq input source hr) (BinaryGeneralResourceRun.mapResult result):=by
  rcases result with ⟨option,pos⟩
  cases option with
  | none=>rfl
  | some state=>
      change (some (sourceState input source hr state),pos)=(some (transportState (capacity_eq input source hr) state.reference),pos)
      rw [sourceState_transport]

theorem run_source_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) :
    sourceResult input source hr (run input hC N bits)=(rationalResourceMachine source.length).run N (.ready source.initialState) bits:=by
  rw [sourceResult_transport]
  have he:=BinaryGeneralResourceRun.run_refines hC.2.1 N (initial input hC) bits
  change BinaryGeneralResourceRun.mapResult (run input hC N bits)=_ at he
  rw [he,resource_run_transport,initial_transport input source hC hr]

theorem run_phase_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) :
    sourceResult input source hr (run input hC N bits)=
      WordRestrictedIndexedRefinement.eraseResult source.TerminalState (source.phase.run N source.start bits):=by
  have he:=WordRestrictedIndexedRefinement.run_refines (rationalResourceMachine source.length)
    source.CursorInvariant source.TerminalState source.phaseProof N bits source.start
  exact (run_source_refines input source hC hr N bits).trans he.symm


theorem reachedGrouping_admissible {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N→Bool) (result : Certified input.length) (hSuccess : (run input hC N bits).1=some result) :
    ∃ terminal : RationalTerminalLotto n,(groupingInput input result).Refines terminal:=by
  obtain ⟨source,hr⟩:=hAd
  exact ⟨reachedTerminal input source hC hr N bits result hSuccess,
    reachedGrouping_refines input source hC hr N bits result hSuccess⟩

noncomputable def phaseResult {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) (result : Certified input.length)
    (hSuccess : (run input hC N bits).1=some result) : source.PhaseResult:=
  ⟨sourceState input source hr result,sourceState_invariant input source hr result
    (run_invariant input source hC hr N bits result hSuccess),run_terminal input hC N bits result hSuccess⟩

theorem run_phase_success {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) (result : Certified input.length)
    (hSuccess : (run input hC N bits).1=some result) :
    (source.phase.run N source.start bits).1=some (phaseResult input source hC hr N bits result hSuccess):=by
  have he:=congrArg Prod.fst (run_phase_refines input source hC hr N bits)
  change (run input hC N bits).1.map (sourceState input source hr)=(source.phase.run N source.start bits).1.map Subtype.val at he
  rw [hSuccess,Option.map_some] at he
  cases hs : (source.phase.run N source.start bits).1 with
  | none=>rw [hs,Option.map_none] at he; cases he
  | some value=>
      rw [hs,Option.map_some] at he
      have hv : value=phaseResult input source hC hr N bits result hSuccess:=by
        apply Subtype.ext
        exact (Option.some.inj he).symm
      rw [hv]

theorem reachedTerminal_eq_phase_data {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) (result : Certified input.length)
    (hSuccess : (run input hC N bits).1=some result) :
    reachedTerminal input source hC hr N bits result hSuccess=source.terminalData (phaseResult input source hC hr N bits result hSuccess):=rfl

theorem run_phase_position {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) :
    (run input hC N bits).2=(source.phase.run N source.start bits).2:=
  congrArg Prod.snd (run_phase_refines input source hC hr N bits)

theorem run_phase_failure_iff {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (N : ℕ) (bits : Fin N→Bool) :
    (run input hC N bits).1=none ↔ (source.phase.run N source.start bits).1=none:=by
  have he:=congrArg Prod.fst (run_phase_refines input source hC hr N bits)
  change (run input hC N bits).1.map (sourceState input source hr)=(source.phase.run N source.start bits).1.map Subtype.val at he
  have hn:=congrArg (·=none) he
  exact Eq.to_iff (by simpa only [Option.map_eq_none_iff] using hn)

end Blotto.BinaryLottoResourceInput
