import Blotto.BinaryPRGHeapResourceUpdateBudget
import Blotto.BinaryPRGWordControllerBooleanResourceThreeWork

/-! The existing three-coordinate rank-height invariant prices actual physical
pair/coin operations and selected tape updates, without a unit-box/lattice
substitution. -/

namespace Blotto.BinaryPRGHeapResourceThreeStep
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore (Store lookup lookup_write)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGWordControllerBooleanResourceThreeWork (threeReference widthBound)
open BinaryPRGWordControllerBooleanResourceThreeBridge
open BinaryThreeResourceHeight (StateHeight resourceHeight coinWidth)

variable {capacity : Store} {hCount : 3 = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

def HeightInv (C s : ℕ) (state : Finished capacity 3 hCount) : Prop :=
  StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state.reference)

theorem selected_height (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (limits : Stored capacity.tree) (state : Finished capacity 3 hCount)
    (h : HeightInv C s state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice
      (hC := hC) state first second tail he).outputs) (branch : Bool) :
    HeightInv C s (BinaryPRGHeapResourceLoop.selectWithWork limits state
      first second tail he outputs hOutputs branch).1 := by
  let choice := BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he
  have hNext := BinaryPRGWordControllerBooleanResourceThreeWork.selected_height
    C s hs choice hCap h branch
  unfold HeightInv
  rw [BinaryPRGHeapResourceLoop.selectWithWork_reference]
  exact hNext

def pairBound (C s depth indexWidth seedCap K H : ℕ) : ℕ :=
  BinaryPRGWordControllerBooleanResourcePair.bound depth (widthBound C s) +
    2 * BinaryPRGHeapStoredTree.readBound K depth +
    2 * BinaryPRGHeapStoredTree.readBound H depth +
    BinaryWordIndexCoinController.sampleBound (coinWidth C s) indexWidth seedCap + 11

theorem pair_coin_bound (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity 3 hCount) (h : HeightInv C s state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (K H : ℕ) (hK : limits.heap.tape.length ≤ K) (hH : state.heap.tape.length ≤ H) :
    (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits state first second tail he).2 +
      (BinaryWordIndexCoinController.sample seed
        (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC)
          limits state first second tail he).1.probability pc hp).2 + 8 ≤
      pairBound C s capacity.width seed.width seed.cap.value K H := by
  let choice := BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he
  have hActive := state.certified.choose_spec.2.symm.trans he
  have hFields := BinaryPRGWordControllerBooleanResourceThreeWork.source_height
    (hC := hC) C s state.reference hCap h first second tail hActive
  have hTrace := (BinaryPRGWordControllerBooleanResourcePair.source capacity.tree state.reference.state
    first second tail hC state.reference.canonical state.reference.interior hActive).trace_wordBounds
    hFields (hs.trans (expressionHeightBudget_ge_input s _))
  have hPair := BinaryPRGWordControllerBooleanResourcePair.pairWithWork_bound
    capacity.tree state.reference.state first second tail hC state.reference.canonical
    state.reference.interior hActive (widthBound C s) hTrace
  have hRead := BinaryPRGHeapResourcePairBudget.pairWithWork_readBound
    (hC := hC) limits state first second tail he
  have hNativeWidth := BinaryThreeResourceHeight.probability_width C s hs hCap
    (choice_toThree choice.original).original h
  have hWord : choice.outputs.probability = (choice_toThree choice.original).original.probability :=
    (BinaryPRGWordControllerBooleanResourceLoop.Choice.probability_original choice).trans
      (BinaryPRGWordControllerThreeChoice.Choice.probability_original (choice_toThree choice.original))
  have hPhysical := congrArg
    (fun outputs : BinaryPRGWordControllerPairOutputs.Outputs => width outputs.probability)
    (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he)
  have hWidth := hPhysical.trans_le ((congrArg width hWord).le.trans hNativeWidth)
  have hCoin := BinaryWordIndexCoinController.sample_bound seed _ pc hp _ hWidth
  have hSpan := Nat.mul_le_mul_left (BinaryWordIndexCoinController.allowance (coinWidth C s) seed.width)
    (Nat.add_le_add_right (Nat.sub_le seed.cap.value pc.value) 1)
  have hCapRead := BinaryPRGHeapResourceCoinBudget.readBound_mono (depth := capacity.width) hK
  have hStateRead := BinaryPRGHeapResourceCoinBudget.readBound_mono (depth := capacity.width) hH
  unfold pairBound BinaryWordIndexCoinController.sampleBound at *
  omega

theorem selectWithWork_bound (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (limits : Stored capacity.tree) (state : Finished capacity 3 hCount) (h : HeightInv C s state)
    (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice
      (hC := hC) state first second tail he).outputs) (branch : Bool)
    (K H P : ℕ) (hK : limits.heap.tape.length ≤ K) (hP : 0 < P)
    (hSpace : state.heap.tape.length + BinaryPRGHeapResourceUpdateBudget.growth
      capacity.width (widthBound C s) P ≤ H) (hRoom : H < 2^P) :
    (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
      outputs hOutputs branch).1.heap.tape.length ≤ state.heap.tape.length +
        BinaryPRGHeapResourceUpdateBudget.growth capacity.width (widthBound C s) P ∧
      (BinaryPRGHeapResourceLoop.selectWithWork limits state first second tail he
        outputs hOutputs branch).2 ≤
        BinaryPRGHeapResourceUpdateBudget.updateBound K H capacity.width (widthBound C s) 3 := by
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
  have hLength : tail.length ≤ 3 := by
    have hn := state.active_length_le
    rw [he] at hn
    simp only [List.length_cons] at hn
    omega
  exact BinaryPRGHeapResourceUpdateBudget.updateWithWork_bound limits state first second tail chosen
    K H (widthBound C s) P 3 hK (by unfold widthBound; omega) hP hSpace hRoom hLength
    hOld hLimits hChosen hTotal hOther hNext

end Blotto.BinaryPRGHeapResourceThreeStep
