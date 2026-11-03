import Blotto.BinaryPRGHeapLoopLifetime
import Blotto.BinaryPRGHeapResourceThreeStep

/-! Source lattice and three-coordinate rank heights derive all actual
selected physical update trace premises. No price/word-height oracle is
required by the resulting invariant-indexed callers. -/

namespace Blotto.BinaryPRGHeapSelectedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup lookup_write)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapResourceUpdateBudget (growth)
open BinaryPRGHeapTraceUsage
open BinaryPRGWordControllerBooleanResourceThreeWork (widthBound)
open BinaryPRGHeapResourceThreeStep (HeightInv selected_height)
open BinaryThreeResourceHeight (resourceHeight)
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

theorem select_usage (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) (B : ℕ)
    (h : usage (BinaryPRGHeapUpdateLifetime.updateWithTrace limits state first second tail
      (if branch then outputs.upper else outputs.lower)).2 ≤ B) :
    usage (BinaryPRGHeapLoopLifetime.selectWithTrace limits state first second tail he outputs hOutputs branch).2 ≤ B + 20 := by
  have hw := wrap_usage 16 2 [(BinaryPRGHeapUpdateLifetime.updateWithTrace limits state first second tail
    (if branch then outputs.upper else outputs.lower)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  unfold BinaryPRGHeapLoopLifetime.selectWithTrace
  dsimp only
  omega

theorem select_lattice_usage (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D
      (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (hs : BinaryPRGHeapResourceInvariant.latticeInv D state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice
      (hC := hC) state first second tail he).outputs) (branch : Bool)
    (C H P : ℕ) (hCHeap : limits.heap.tape.length ≤ C) (hP : 0 < P)
    (hSpace : state.heap.tape.length + growth capacity.width
      (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) P ≤ H)
    (hRoom : H < 2^P) :
    usage (BinaryPRGHeapLoopLifetime.selectWithTrace limits state first second tail he outputs hOutputs branch).2 ≤
      BinaryPRGHeapUpdateLifetime.updateEnvelope C H capacity.width
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) + 20 := by
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  let choice := BinaryPRGHeapResourceLoop.logicalChoice (hC := hC)
    state first second tail he
  let chosen := if branch then outputs.upper else outputs.lower
  let a := state.packed.readWithWork first.word
  let b := state.packed.readWithWork second.word
  let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let selected := BinaryPRGHeapResourceLoop.selectWithWork limits state
    first second tail he outputs hOutputs branch
  have hu := fun j => (hBox j).2
  have hChosenEq : chosen = choice.endpoint branch := by
    dsimp only [chosen,BinaryPRGWordControllerBooleanResourceLoop.Choice.endpoint]
    rw [hOutputs]
  have hChoice : BinaryGeneralResourceLattice.StateInvariant
      (table capacity.cap capacity.tree n hCount) D choice.original.original.state := hs
  have hChosenNative := BinaryGeneralResourceExecution.selected_endpoint_width
    choice.original.original D hD hLattice hu hChoice branch
  rw [← choice.original.endpoint_original,← choice.endpoint_original] at hChosenNative
  have hChosenWidth : width chosen ≤ W := by
    rw [hChosenEq]
    unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  have hTotalNative := BinaryGeneralResourceExecution.selected_total_width
    choice.original.original D hD hLattice hu hChoice
  have hOtherNative := BinaryGeneralResourceExecution.selected_other_width
    choice.original.original D hD hLattice hu hChoice branch
  rw [← choice.original.endpoint_original,← choice.endpoint_original] at hOtherNative
  simp only [BinaryPRGWordControllerGeneralChoice.Choice.original,
    BinaryPRGWordControllerBooleanResourceLoop.Choice.original,
    BinaryPRGWordControllerBooleanResourceLoop.Certified.reference_state,
    BinaryPRGWordControllerBooleanResourceUpdate.State.reference,
    BinaryPRGWordControllerBooleanResourceUpdate.table_read] at hTotalNative hOtherNative
  have hReadA := BinaryPRGHeapPackedStore.Packed.readWithWork_value
    state.packed state.packed_realizes first.word
  have hReadB := BinaryPRGHeapPackedStore.Packed.readWithWork_value
    state.packed state.packed_realizes second.word
  have hA : BinaryRationalOpcode.Valid a.1 := by
    rw [hReadA]; exact (state.reference.canonical first).1
  have hB : BinaryRationalOpcode.Valid b.1 := by
    rw [hReadB]; exact (state.reference.canonical second).1
  have hAdd := BinaryQuadraticOpcode.applyWithWork_state .add a.1 b.1 hA hB
  have hTotalValid : BinaryRationalOpcode.Valid total.1 := by
    rw [hAdd]
    exact BinaryRationalOpcode.apply_valid .add _ _ hA hB
  have hChosenValid : BinaryRationalOpcode.Valid chosen := by
    rw [hChosenEq]; exact (choice.endpoint_canonical branch).1
  have hSub := BinaryQuadraticOpcode.applyWithWork_state .sub
    total.1 chosen hTotalValid hChosenValid
  have hTotalWidth : width total.1 ≤ W := by
    rw [hAdd,hReadA,hReadB]
    exact hTotalNative
  have hOtherWidth : width other.1 ≤ W := by
    rw [hSub,hAdd,hReadA,hReadB,hChosenEq]
    exact hOtherNative.trans (by
      unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
      omega)
  have hOld : ∀ address : Address capacity.width capacity.cap,
      width (state.packed.readWithWork address.word).1 ≤ W := by
    intro address
    rw [BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes]
    exact BinaryPRGWordControllerBooleanResourceLoopWork.state_width
      D hD state.reference hu hs address
  have hLimit : ∀ address : Address capacity.width capacity.cap,
      width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W := by
    intro address
    rw [BinaryPRGHeapStoredTree.readWithWork_value]
    exact BinaryPRGWordControllerBooleanResourceLoopWork.capacity_width
      D hD hC hLattice hBox address
  have hSelectedInv := BinaryPRGHeapResourceInvariant.selected_lattice
    (hC := hC) D hLattice limits state first second tail he outputs hOutputs branch hs
  have hNext : ∀ address : Address capacity.width capacity.cap,
      width (selected.1.packed.readWithWork address.word).1 ≤ W := by
    intro address
    rw [BinaryPRGHeapPackedStore.Packed.readWithWork_value
      selected.1.packed selected.1.packed_realizes]
    exact BinaryPRGWordControllerBooleanResourceLoopWork.state_width
      D hD selected.1.reference hu hSelectedInv address
  have hUpdate := BinaryPRGHeapUpdateLifetime.updateWithTrace_usage limits state first second tail chosen
    C H W P hCHeap (by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega)
    hP hSpace hRoom hOld hLimit hChosenWidth hTotalWidth hOtherWidth hNext
  exact select_usage limits state first second tail he outputs hOutputs branch _ hUpdate

theorem select_height_usage {hCount3 : 3 = capacity.cap.value} (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount3).read j)) s)
    (limits : Stored capacity.tree) (state : Finished capacity 3 hCount3) (h : HeightInv C s state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice
      (hC := hC) state first second tail he).outputs) (branch : Bool)
    (K H P : ℕ) (hK : limits.heap.tape.length ≤ K) (hP : 0 < P)
    (hSpace : state.heap.tape.length + BinaryPRGHeapResourceUpdateBudget.growth
      capacity.width (widthBound C s) P ≤ H) (hRoom : H < 2^P) :
    usage (BinaryPRGHeapLoopLifetime.selectWithTrace limits state first second tail he outputs hOutputs branch).2 ≤
      BinaryPRGHeapUpdateLifetime.updateEnvelope K H capacity.width (widthBound C s) + 20 := by
  let choice := BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he
  let chosen := if branch then outputs.upper else outputs.lower
  let a := state.packed.readWithWork first.word
  let b := state.packed.readWithWork second.word
  let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let selected := BinaryPRGHeapResourceLoop.selectWithWork limits state
    first second tail he outputs hOutputs branch
  have hChosenEq : chosen = choice.endpoint branch := by
    dsimp only [chosen,BinaryPRGWordControllerBooleanResourceLoop.Choice.endpoint]
    rw [hOutputs]
  let input := BinaryPRGWordControllerBooleanResourcePair.source capacity.tree
    choice.state.state first second tail hC choice.state.canonical choice.state.interior choice.head_pair
  have hFields := BinaryPRGWordControllerBooleanResourceThreeWork.source_height
    (hC := hC) C s choice.state hCap h first second tail choice.head_pair
  have hWords := input.run_wordBounds hFields (hs.trans (expressionHeightBudget_ge_input s _))
  have hChosen : width chosen ≤ widthBound C s := by
    rw [hChosenEq,BinaryPRGWordControllerBooleanResourceLoop.Choice.endpoint,choice.outputs_correct]
    unfold BinaryPRGWordControllerBooleanResourcePair.pair
    cases branch
    · change width (BinaryPRGWordControllerPairOutputs.prepare input).lower ≤ _
      exact (congrArg width (BinaryPRGWordControllerPairOutputs.prepare_words input).1).trans_le (hWords 7)
    · change width (BinaryPRGWordControllerPairOutputs.prepare input).upper ≤ _
      exact (congrArg width (BinaryPRGWordControllerPairOutputs.prepare_words input).2.1).trans_le (hWords 8)
  have hReadA := BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes first.word
  have hReadB := BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes second.word
  have hFirst : BinaryRationalOpcode.Valid a.1 := by rw [hReadA]; exact (state.reference.canonical first).1
  have hSecond : BinaryRationalOpcode.Valid b.1 := by rw [hReadB]; exact (state.reference.canonical second).1
  have hAdd := BinaryQuadraticOpcode.applyWithWork_state .add a.1 b.1 hFirst hSecond
  have hTotal : width total.1 ≤ widthBound C s := by
    have hi : RationalHeight (value a.1) (expressionHeightBudget (resourceHeight C s) 0) := by
      rw [hReadA,expressionHeightBudget_zero]
      exact BinaryPRGWordControllerBooleanResourceThreeWork.resource_height_tree C s state.reference h first
    have hj : RationalHeight (value b.1) (expressionHeightBudget (resourceHeight C s) 0) := by
      rw [hReadB,expressionHeightBudget_zero]
      exact BinaryPRGWordControllerBooleanResourceThreeWork.resource_height_tree C s state.reference h second
    have hn := BinaryRationalOpcode.apply_height_width .add a.1 b.1 hFirst hSecond _ (hi.add_level hj)
    rw [hAdd]
    norm_num [expressionHeightBudget] at hn
    unfold widthBound
    omega
  have hNextLogical := BinaryPRGWordControllerBooleanResourceThreeWork.selected_height
    C s hs choice hCap h branch
  have hOtherData : width (BinaryQuadraticData.apply .sub
      (BinaryQuadraticData.apply .add (lookup state.reference.state.resource first.word)
        (lookup state.reference.state.resource second.word)) (choice.endpoint branch)) ≤ widthBound C s := by
    have hn := BinaryPRGWordControllerBooleanResourceThreeWork.resource_width_tree
      C s (choice.select branch) hNextLogical choice.second
    simp only [BinaryPRGWordControllerBooleanResourceLoop.Choice.select,
      BinaryPRGWordControllerBooleanResourceUpdate.update,lookup_write,ite_true] at hn
    exact hn
  have hOther : width other.1 ≤ widthBound C s := by
    dsimp only [other,total,a,b]
    rw [BinaryQuadraticData.apply_erasure,BinaryQuadraticData.apply_erasure,hReadA,hReadB,hChosenEq]
    exact hOtherData
  have hOld : ∀ address : Address capacity.width capacity.cap,
      width (state.packed.readWithWork address.word).1 ≤ widthBound C s := by
    intro address
    rw [BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes]
    exact BinaryPRGWordControllerBooleanResourceThreeWork.resource_width_tree C s state.reference h address
  have hLimits : ∀ address : Address capacity.width capacity.cap,
      width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ widthBound C s := by
    intro address
    rw [BinaryPRGHeapStoredTree.readWithWork_value]
    exact BinaryPRGWordControllerBooleanResourceThreeWork.capacity_width_tree C s hC hCap address
  have hSelected := selected_height C s hs hCap limits state h first second tail he outputs hOutputs branch
  have hNext : ∀ address : Address capacity.width capacity.cap,
      width (selected.1.packed.readWithWork address.word).1 ≤ widthBound C s := by
    intro address
    rw [BinaryPRGHeapPackedStore.Packed.readWithWork_value selected.1.packed selected.1.packed_realizes]
    exact BinaryPRGWordControllerBooleanResourceThreeWork.resource_width_tree C s selected.1.reference hSelected address
  have hUpdate := BinaryPRGHeapUpdateLifetime.updateWithTrace_usage limits state first second tail chosen
    K H (widthBound C s) P hK (by unfold widthBound; omega) hP hSpace hRoom
    hOld hLimits hChosen hTotal hOther hNext
  exact select_usage limits state first second tail he outputs hOutputs branch _ hUpdate

end Blotto.BinaryPRGHeapSelectedLifetime
