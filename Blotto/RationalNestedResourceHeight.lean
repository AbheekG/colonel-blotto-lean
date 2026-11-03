import Blotto.RationalResourceHeight
import Blotto.RationalTerminalHeight
import Blotto.WordTreeLeafContracts
import Blotto.RationalNestedResourceProgram

/-! Native three-coordinate resource/terminal outputs have linear word size
in input height plus precision. Only the proved rank-two local phase uses the
fixed-round height estimate. Every deterministic fallback is included. -/

namespace Blotto.RationalNestedResourceSystem

def FieldsHeight (i : RationalNestedResourceSystem) (s : ℕ) : Prop :=
  RationalHeight i.M s ∧ (∀ j, RationalHeight (i.long j) s) ∧
    (∀ j, RationalHeight (i.short j) s) ∧ ∀ j, RationalHeight (i.initial j) s

theorem FieldsHeight.mono {i : RationalNestedResourceSystem} {s t : ℕ} (h : i.FieldsHeight s) (hst : s ≤ t) :
    i.FieldsHeight t := ⟨h.1.mono hst, fun j => (h.2.1 j).mono hst,
      fun j => (h.2.2.1 j).mono hst, fun j => (h.2.2.2 j).mono hst⟩

theorem FieldsHeight.capacity {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s) (j : Fin 3) :
    RationalHeight (i.capacity j) (expressionHeightBudget s 1) := by
  have hLong : RationalHeight (i.long j) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.1 j
  have hShort : RationalHeight (i.short j) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.2.1 j
  exact hLong.sub_level hShort

theorem FieldsHeight.phase_resource_leaves {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) : (i.phase.specification i.start).decode.ForLeaves
      (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7)) := by
  have hm := expressionHeightBudget_ge_input s 1
  have hInitial : i.initialState.resource.HeightAt (expressionHeightBudget s 1) := by
    intro j
    rw [i.initialState_allocation]
    exact (h.2.2.2 j).mono hm
  have hRaw := rationalResourceMachine_height_leaves i.capacity 2 _ (hs.trans hm)
    h.capacity (.ready i.initialState) hInitial i.initial_rank
  rw [expressionHeightBudget_comp] at hRaw
  have hEq : (i.phase.specification i.start).map Subtype.val =
      (rationalResourceMachine i.capacity).specification (.ready i.initialState) :=
    (rationalResourceMachine i.capacity).restricted_specification i.CursorInvariant i.TerminalState i.phaseProof i.start
  rw [← hEq] at hRaw
  exact (WordChoiceTree.forLeaves_map_iff _ Subtype.val _).mp hRaw

theorem FieldsHeight.terminalData {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (value : i.PhaseResult) (hResource : value.1.resource.HeightAt (expressionHeightBudget s 7)) :
    (i.terminalData value).FieldsHeight (expressionHeightBudget s 7) := by
  have hm := expressionHeightBudget_ge_input s 7
  exact ⟨h.1.mono hm, fun j => (h.2.1 j).mono hm, fun j => (h.2.2.1 j).mono hm, hResource⟩

theorem FieldsHeight.machine_leaves {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.machine K outerBits scalarBits).specification i.samplingStart).decode.ForLeaves
      (fun x => ∀ j, RationalHeight (x j) (expressionHeightBudget (max s (K + 2)) 57)) := by
  let w := max s (K + 2)
  have hW := h.mono (le_max_left s (K + 2))
  have hw : 2 ≤ w := hs.trans (le_max_left _ _)
  rw [machine, samplingStart, WordStateMachine.serial_source_specification]
  apply WordChoiceTree.bind_forLeaves_of _ _ (fun value => value.1.resource.HeightAt (expressionHeightBudget w 7))
  · exact hW.phase_resource_leaves hw
  · intro value hValue
    apply RationalSegmentLottery.machine_forLeaves
    intro slot j
    have hm := expressionHeightBudget_ge_input w 7
    have hPoint := (hW.terminalData value hValue).point (hw.trans hm) K outerBits scalarBits slot j
    rw [max_eq_left ((le_max_right s (K + 2)).trans hm), expressionHeightBudget_comp] at hPoint
    exact hPoint

theorem FieldsHeight.fallback {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (j : Fin 3) :
    RationalHeight (i.fallback K outerBits scalarBits j) (expressionHeightBudget (max s (K + 2)) 57) :=
  (i.machine K outerBits scalarBits).chooseLeaf_forLeaves i.samplingStart _ (h.machine_leaves hs K outerBits scalarBits) j

theorem FieldsHeight.fixedSample {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) (j : Fin 3) :
    RationalHeight (i.fixedSample K R outerBits scalarBits choiceBits j) (expressionHeightBudget (max s (K + 2)) 57) := by
  rw [RationalNestedResourceSystem.fixedSample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (h.machine_leaves hs K outerBits scalarBits)
    (h.fallback hs K outerBits scalarBits) j

theorem FieldsHeight.sample {i : RationalNestedResourceSystem} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) (j : Fin 3) :
    RationalHeight (i.sample K bits j) (expressionHeightBudget (max s (K + 2)) 57) :=
  h.fixedSample hs K _ _ _ _ j

end Blotto.RationalNestedResourceSystem
