import Blotto.BinaryReflectedPhaseRefinement
import Blotto.RationalFourSmallHeight

/-! Actual successful reflected resource runs derive reached resource,
terminal and eighteen-slot profile heights from the original six-word source.
The local rank-two phase is retained; no reached-state/profile height oracle
is supplied. This is a size dependency, not a whole-controller work claim. -/

namespace Blotto.BinaryReflectedReachedHeight
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedPhaseRefinement

theorem phase_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) :
    (phaseResult input source hC hR hCase N bits result hSuccess).1.resource.HeightAt (expressionHeightBudget s 21) := by
  let system := source.reflectedResourceSystem hCase
  have hSystem := hH.reflectedResourceSystem hs hCase
  have hs14 := hs.trans (expressionHeightBudget_ge_input s 14)
  have hLeaves := hSystem.phase_resource_leaves hs14
  let P := fun value : system.PhaseResult => value.1.resource.HeightAt (expressionHeightBudget (expressionHeightBudget s 14) 7)
  let fallback := system.phase.chooseLeaf system.start
  have hFallback : P fallback := system.phase.chooseLeaf_forLeaves system.start P hLeaves
  have hOutput := WordChoiceTree.output_forLeaves N (system.phase.specification system.start) fallback bits P hLeaves hFallback
  rw [← system.phase.output_refines] at hOutput
  unfold WordStateMachine.output at hOutput
  rw [setupRun_phase_success input source hC hR hCase N bits result hSuccess] at hOutput
  dsimp only [Option.getD_some,P] at hOutput
  rw [expressionHeightBudget_comp] at hOutput
  exact hOutput

theorem reached_resource_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (j : Fin 3) :
    RationalHeight (value (result.state.resource.read j)) (expressionHeightBudget s 21) := by
  have h := phase_height input source hC hR hCase s hs hH N bits result hSuccess j
  dsimp only [phaseResult] at h
  rw [BinaryReachedTerminal.sourceState_allocation] at h
  exact h

theorem terminal_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) :
    ((source.reflectedResourceSystem hCase).terminalData (phaseResult input source hC hR hCase N bits result hSuccess)).FieldsHeight
      (expressionHeightBudget s 21) := by
  have hSystem := hH.reflectedResourceSystem hs hCase
  have hPhase := phase_height input source hC hR hCase s hs hH N bits result hSuccess
  have hPhaseRaw : (phaseResult input source hC hR hCase N bits result hSuccess).1.resource.HeightAt
      (expressionHeightBudget (expressionHeightBudget s 14) 7) := by rw [expressionHeightBudget_comp]; exact hPhase
  have ht := hSystem.terminalData (phaseResult input source hC hR hCase N bits result hSuccess) hPhaseRaw
  rw [expressionHeightBudget_comp] at ht
  exact ht

theorem profile_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (((source.reflectedResourceSystem hCase).terminalData (phaseResult input source hC hR hCase N bits result hSuccess)).profile K outer).HeightAt
      (expressionHeightBudget (max s (K + 2)) 68) := by
  let W := max s (K + 2)
  have hsW : 2 ≤ W := hs.trans (le_max_left _ _)
  have hFields := hH.mono (le_max_left s (K + 2))
  have hTerminal := terminal_height input source hC hR hCase W hsW hFields N bits result hSuccess
  have hProfile := hTerminal.profile (hsW.trans (expressionHeightBudget_ge_input W 21)) K outer
  have hPrecision : K + 2 ≤ expressionHeightBudget W 21 := (le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input W 21)
  rw [max_eq_left hPrecision,expressionHeightBudget_comp] at hProfile
  exact hProfile

end Blotto.BinaryReflectedReachedHeight
