import Blotto.BinaryThreeResourceFallbackWork
import Blotto.BinaryTerminalFallback
import Blotto.BinaryReflectedFactoryPrepared

/-! The deterministic lower resource leaf derives its resource, terminal,
profile, prepared-input and selected-emission heights/prices from original
six-word fields. These are leaf guarantees, including zero-mass successors;
no successful random run or caller-supplied reached-height oracle is needed. -/

namespace Blotto.BinaryReflectedFallbackHeight
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup

theorem phase_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (_hC : input.Canonical) (_hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (((source.reflectedResourceSystem hCase).phase.chooseLeaf (source.reflectedResourceSystem hCase).start).1.resource).HeightAt
      (expressionHeightBudget s 21) := by
  have hSystem := hH.reflectedResourceSystem hs hCase
  have hLeaves := hSystem.phase_resource_leaves (hs.trans (expressionHeightBudget_ge_input s 14))
  have hLeaf := (source.reflectedResourceSystem hCase).phase.chooseLeaf_forLeaves
    (source.reflectedResourceSystem hCase).start _ hLeaves
  rw [expressionHeightBudget_comp] at hLeaf
  exact hLeaf

theorem resource_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (j : Fin 3) :
    RationalHeight (value ((BinaryResourceFallback.setup input hC).state.resource.read j)) (expressionHeightBudget s 21) := by
  have h := phase_height input source hC hR hCase s hs hH j
  rw [← BinaryTerminalFallback.sourceState_eq_phase_leaf input source hC hR hCase] at h
  change RationalHeight ((BinaryTerminalFallback.sourceState input source hC hR hCase).resource.allocation j) _ at h
  change RationalHeight ((BinaryReachedTerminal.sourceState input source hC hR hCase (BinaryResourceFallback.setup input hC)).resource.allocation j) _ at h
  rw [BinaryReachedTerminal.sourceState_allocation] at h
  exact h

theorem terminal_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (BinaryTerminalFallback.terminal input source hC hR hCase).FieldsHeight (expressionHeightBudget s 21) := by
  have hSystem := hH.reflectedResourceSystem hs hCase
  have hPhase := phase_height input source hC hR hCase s hs hH
  have hPhaseRaw : (((source.reflectedResourceSystem hCase).phase.chooseLeaf (source.reflectedResourceSystem hCase).start).1.resource).HeightAt
      (expressionHeightBudget (expressionHeightBudget s 14) 7) := by rw [expressionHeightBudget_comp]; exact hPhase
  have ht := hSystem.terminalData ((source.reflectedResourceSystem hCase).phase.chooseLeaf (source.reflectedResourceSystem hCase).start) hPhaseRaw
  rw [expressionHeightBudget_comp] at ht
  rw [BinaryTerminalFallback.terminal_eq_phase_leaf]
  exact ht

theorem profile_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer : Fin K → Bool) :
    ((BinaryTerminalFallback.terminal input source hC hR hCase).profile K outer).HeightAt
      (expressionHeightBudget (max s (K + 2)) 68) := by
  let W := max s (K + 2)
  have hTerminal := terminal_height input source hC hR hCase W (hs.trans (le_max_left _ _)) (hH.mono (le_max_left _ _))
  have hProfile := hTerminal.profile ((hs.trans (le_max_left _ _)).trans (expressionHeightBudget_ge_input W 21)) K outer
  have hk : K + 2 ≤ expressionHeightBudget W 21 := (le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input W 21)
  rw [max_eq_left hk,expressionHeightBudget_comp] at hProfile
  exact hProfile

theorem input_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    BinaryNestedParameterWork.InputHeight (BinaryNestedTerminalPreparationWork.prepareWithWork
      (prepare input) (BinaryResourceFallback.setup input hC).state).1.1 (expressionHeightBudget s 23) := by
  rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state]
  have hRef := BinaryNestedTerminalInput.prepare_refines _ _ _ (prepare_canonical input hC)
    (BinaryResourceFallback.setup input hC).canonical (BinaryTerminalFallback.terminal_data_refines input source hC hR hCase)
  have hHeight := (terminal_height input source hC hR hCase s hs hH).input
  rw [expressionHeightBudget_comp] at hHeight
  exact BinaryNestedTerminalPreparationWork.input_height_of_refines _ _ hRef _ hHeight

theorem terminal_input_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (BinaryNestedTerminalPreparationWork.prepareWithWork (prepare input) (BinaryResourceFallback.setup input hC).state).2 ≤
      BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) := by
  have hSystem := hH.reflectedResourceSystem hs hCase
  have hRef := prepare_refines input source hC hR hCase
  have hm := expressionHeightBudget_mono s (by decide : 14 ≤ 21)
  apply BinaryNestedTerminalPreparationWork.prepareWithWork_bound _ _ (prepare_canonical input hC) (BinaryResourceFallback.setup input hC).canonical
  · refine ⟨?_,?_,?_⟩
    · rw [hRef.1]; exact hSystem.1.mono hm
    · intro j; rw [hRef.2.1 j]; exact (hSystem.2.1 j).mono hm
    · intro j; rw [hRef.2.2.1 j]; exact (hSystem.2.2.1 j).mono hm
  · exact resource_height input source hC hR hCase s hs hH

theorem factory_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer : Fin K → Bool) :
    (BinaryNestedSpecFactoryWork.profileWithWork (BinaryNestedTerminalPreparationWork.prepareWithWork
      (prepare input) (BinaryResourceFallback.setup input hC).state).1.1 K outer).2 ≤ BinaryReflectedFactoryPrepared.bound s K := by
  have hc : (BinaryNestedTerminalPreparationWork.prepareWithWork (prepare input) (BinaryResourceFallback.setup input hC).state).1.1.Canonical := by
    rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state]
    exact BinaryNestedTerminalInput.prepare_canonical _ _ (prepare_canonical input hC) (BinaryResourceFallback.setup input hC).canonical
  have hs23 : 3 ≤ expressionHeightBudget s 23 := by unfold expressionHeightBudget; omega
  exact BinaryNestedSpecFactoryWork.profileWithWork_bound _ hc _ hs23 (input_height input source hC hR hCase s hs hH) K outer

theorem selected_emission_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    (BinaryReflectedSelectedEmissionWork.sampleWithWork input (BinaryTerminalFallback.table input hC K outer) slot K scalar).2 ≤
      BinaryReflectedSelectedEmissionWork.bound s K := by
  let table := BinaryTerminalFallback.table input hC K outer
  let terminal := BinaryTerminalFallback.terminal input source hC hR hCase
  let W := max s (K + 2)
  have hc := BinaryTerminalFallback.table_canonical input hC K outer
  have hr := BinaryTerminalFallback.table_refines input source hC hR hCase K outer
  have hh := profile_height input source hC hR hCase s hs hH K outer
  have hs68 : 2 ≤ expressionHeightBudget W 68 := hs.trans ((le_max_left _ _).trans (expressionHeightBudget_ge_input W 68))
  have hPoint := BinarySegmentPoint.sampleWork_bound table (terminal.profile K outer) hc hr _ hs68 hh.2 slot K scalar
  have hk : K + 2 ≤ expressionHeightBudget W 68 := (le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input W 68)
  have hRowC := BinarySegmentPoint.sample_canonical table slot K scalar hc
  have hRowH : ∀ j, RationalHeight (value ((BinarySegmentPoint.sample table slot K scalar).read j)) (expressionHeightBudget W 71) := by
    intro j
    rw [BinarySegmentPoint.sample_value table (terminal.profile K outer) hc hr]
    have he := hh.point hs68 K slot scalar j
    rw [max_eq_left hk,expressionHeightBudget_comp] at he
    exact he
  have hLengths : ∀ j, RationalHeight (value ((originalLengths input).read j)) (expressionHeightBudget W 71) := by
    intro j
    rw [originalLengths_value input source hR j]
    exact (hH.originalLengths j).mono ((le_max_left _ _).trans (expressionHeightBudget_ge_input W 71))
  have hReflect := BinaryReflectedSelectedEmissionWork.reflectWithWork_bound input (BinarySegmentPoint.sample table slot K scalar) hC hRowC _ hLengths hRowH
  exact Nat.add_le_add hPoint hReflect

end Blotto.BinaryReflectedFallbackHeight
