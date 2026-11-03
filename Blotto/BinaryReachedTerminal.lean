import Blotto.BinarySharedResourceRun
import Blotto.BinaryReflectedTerminalEmission

/-! Successful actual Boolean resource rounding derives every terminal
constructor/descriptor/emission premise from the original six-word input.
No caller supplies a resource invariant or terminal factory. Full serial
categorical execution under the same cap remains a separate composition. -/

namespace Blotto.BinaryReachedTerminal
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinaryThreeResourcePair BinarySharedResourceRun BinaryNestedTerminalInput

noncomputable def sourceState (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (result : Certified (prepare input).capacity) : RationalActiveResources (source.reflectedResourceSystem hCase).capacity where
  resource := RationalResourceArray.ofAllocation (fun j => value (result.state.resource.read j))
  active := result.state.active
  nodup := result.nodup
  membership := by
    intro j
    rw [RationalResourceArray.allocation_ofAllocation]
    have hCap := capacity_value (prepare input) (source.reflectedResourceSystem hCase) (prepare_canonical input hC)
      (prepare_refines input source hC hr hCase) j
    rw [← hCap]
    exact result.membership j

theorem sourceState_allocation (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (result : Certified (prepare input).capacity) (j : Fin 3) :
    (sourceState input source hC hr hCase result).resource.allocation j = value (result.state.resource.read j) :=
  congrFun (RationalResourceArray.allocation_ofAllocation _) j

theorem sourceState_invariant (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) :
    RationalResourceInvariant (source.reflectedResourceSystem hCase).capacity
      ((source.reflectedResourceSystem hCase).totalResource : ℝ) (sourceState input source hC hr hCase result) := by
  have ht := setupRun_terminal_contract input source hC hr hCase N bits result hSuccess
  have hCap := capacity_value (prepare input) (source.reflectedResourceSystem hCase) (prepare_canonical input hC)
    (prepare_refines input source hC hr hCase)
  have hRow : (sourceState input source hC hr hCase result).resource.realAllocation =
      fun j => (value (result.state.resource.read j) : ℝ) := by
    funext j
    exact congrArg (fun q : ℚ => (q : ℝ)) (sourceState_allocation input source hC hr hCase result j)
  unfold RationalResourceInvariant
  rw [hRow]
  refine ⟨?_,ht.2.2⟩
  intro j
  have hb := ht.2.1 j
  dsimp only at hb ⊢
  rw [hCap j] at hb
  exact hb

noncomputable def terminal (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) : RationalTerminalResources :=
  (source.reflectedResourceSystem hCase).terminal (sourceState input source hC hr hCase result)
    (sourceState_invariant input source hC hr hCase N bits result hSuccess)
    (setupRun_terminal_contract input source hC hr hCase N bits result hSuccess).1

theorem terminal_data_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) :
    DataRefines (prepare input) result.state (terminal input source hC hr hCase N bits result hSuccess) :=
  BinaryNestedTerminalInput.terminal_data_refines _ _ _ _ _ _ (prepare_refines input source hC hr hCase)
    (fun j => (sourceState_allocation input source hC hr hCase result j).symm)

theorem profile_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer).Refines
      ((terminal input source hC hr hCase N bits result hSuccess).profile K outer) :=
  BinaryTerminalProfileCompiler.profile_refines _ _ _ (prepare_canonical input hC) result.canonical
    (terminal_data_refines input source hC hr hCase N bits result hSuccess) K outer

theorem emission_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    FullBudget (source.B : ℝ)
      (fun j => (value ((BinaryReflectedTerminalEmission.sample input result.state K outer scalar slot).read j) : ℝ)) :=
  BinaryReflectedTerminalEmission.sample_fullBudget input source result.state _ hC hr hCase result.canonical
    (terminal_data_refines input source hC hr hCase N bits result hSuccess) K outer scalar slot

theorem emission_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j => (value ((BinaryReflectedTerminalEmission.sample input result.state K outer scalar slot).read j) : ℝ)) :=
  BinaryReflectedTerminalEmission.sample_inBox input source result.state _ hC hr result.canonical
    (terminal_data_refines input source hC hr hCase N bits result hSuccess) K outer scalar slot

end Blotto.BinaryReachedTerminal
