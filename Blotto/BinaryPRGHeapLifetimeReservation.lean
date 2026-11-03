import Blotto.BinaryPRGHeapSelectedLifetime
import Blotto.BinaryPRGHeapLoopLifetimeBudget
import Blotto.BinaryPRGHeapResourceThreeReservation

/-! Original lattice and reflected rank-height promises instantiate the whole
physical loop's allocation budget. Retained tape room decreases with the active
list; all old allocations in the trace remain counted. -/

namespace Blotto.BinaryPRGHeapLifetimeReservation
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address table)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage BinaryPRGHeapPairLifetime
open BinaryPRGHeapLoopLifetimeBudget (ReachableBudget)
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def coinEnvelope (W indexWidth seedCap : ℕ) : ℕ :=
  BinaryWordCoinLifetime.sampleBound W indexWidth seedCap + seedCap + 2 * W + 2 * indexWidth + 24

theorem coin_usage (seed : BinarySeedLookupTree.Store) (word : SignedWord)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (W : ℕ) (hW : width word ≤ W) :
    usage (BinaryWordCoinLifetime.sampleWithTrace seed word pc hp).2 ≤ coinEnvelope W seed.width seed.cap.value := by
  have h := BinaryWordCoinLifetime.sampleWithTrace_bounds seed word pc hp W hW
  have hSpan := Nat.sub_le seed.cap.value pc.value
  have hm := Nat.mul_le_mul_right (BinaryWordCoinLifetime.localBound W seed.width)
    (Nat.add_le_add_right hSpan 1)
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells coinEnvelope BinaryWordCoinLifetime.sampleBound at *
  omega

def stepEnvelope (C H depth pairW coinW indexWidth seedCap : ℕ) : ℕ :=
  max (pairEnvelope C H depth pairW + coinEnvelope coinW indexWidth seedCap)
    (BinaryPRGHeapUpdateLifetime.updateEnvelope C H depth pairW + 20)

theorem pairCoin_usage (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first :: second :: tail)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (C H W Q : ℕ)
    (hCHeap : limits.heap.tape.length ≤ C) (hH : state.heap.tape.length ≤ H)
    (hTrace : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code
      (BinaryPRGHeapResourceLoop.sourceWithWork (hC := hC) limits state first second tail he).1.inputs W)
    (hCoin : width (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits state first second tail he).1.probability ≤ Q) :
    let prepared := pairWithTrace (hC := hC) limits state first second tail he
    usage prepared.2 + usage (BinaryWordCoinLifetime.sampleWithTrace seed prepared.1.probability pc hp).2 ≤
      stepEnvelope C H capacity.width W Q seed.width seed.cap.value := by
  have hPair := pairWithTrace_usage (hC := hC) limits state first second tail he C H W hCHeap hH hTrace
  have hWidth : width (pairWithTrace (hC := hC) limits state first second tail he).1.probability ≤ Q := by
    rw [pairWithTrace_erasure]
    exact hCoin
  have hc := coin_usage seed _ pc hp Q hWidth
  exact (Nat.add_le_add hPair hc).trans (le_max_left _ _)

theorem lattice_budget (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (C H P : ℕ) (hCHeap : limits.heap.tape.length ≤ C) (hP : 0 < P) (hRoom : H < 2^P) :
    ReachableBudget (n := n) (hCount := hCount) seed limits hC
      (BinaryPRGHeapResourceReservation.Reserved (n := n) (hCount := hCount) D P H)
      (stepEnvelope C H capacity.width (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D)
        (1 + 2 * binaryWordWidth D) seed.width seed.cap.value) := by
  refine ⟨?_,?_,?_⟩
  · intro state first second tail he pc hp hs
    have hHeap : state.heap.tape.length ≤ H := by have h := hs.2; omega
    have hActive : state.reference.state.active = first :: second :: tail := state.certified.choose_spec.2.symm.trans he
    have hNative : state.reference.reference.state.active = first.index n hCount :: second.index n hCount ::
        tail.map (fun address => address.index n hCount) := by
      rw [state.reference.reference_state]
      simp only [BinaryPRGWordControllerBooleanResourceUpdate.State.reference,hActive,List.map_cons]
    have ht := BinaryGeneralResourceLattice.pair_trace_wordBounds
      (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC) state.reference.reference
      (first.index n hCount) (second.index n hCount) (tail.map (fun address => address.index n hCount))
      hNative D hD hLattice (fun j => (hBox j).2) hs.1
    rw [← BinaryPRGWordControllerBooleanResourcePair.source_reference capacity.tree state.reference.state
      first second tail hC state.reference.canonical state.reference.interior hActive n hCount
      (BinaryPRGWordControllerBooleanResourceLoop.capCanonical capacity n hCount hC)
      state.reference.reference state.reference.reference_state] at ht
    have hTrace : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code
        (BinaryPRGHeapResourceLoop.sourceWithWork (hC := hC) limits state first second tail he).1.inputs
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D) := by
      simpa only [BinaryPRGHeapResourceLoop.sourceWithWork_value,
        BinaryPRGWordControllerBooleanResourceLoopWork.widthBound] using ht
    exact pairCoin_usage seed limits state first second tail he pc hp C H _ _ hCHeap hHeap hTrace
      (BinaryPRGHeapResourceCoinBudget.pair_probability_width (hC := hC) D hD hLattice
        (fun j => (hBox j).2) limits state hs.1 first second tail he)
  · intro state first second tail he outputs hOutputs branch hs
    exact (BinaryPRGHeapSelectedLifetime.select_lattice_usage D hD hLattice hBox limits state hs.1
      first second tail he outputs hOutputs branch C H P hCHeap hP
      (BinaryPRGHeapResourceReservation.reserved_room D P H state hs first second tail he) hRoom).trans
        (le_max_right _ _)
  · intro state first second tail he outputs hOutputs branch hs
    rw [BinaryPRGHeapLoopLifetime.selectWithTrace_erasure]
    exact (BinaryPRGHeapResourceReservation.select_reserved D hD hLattice hBox limits state first second tail he
      outputs hOutputs branch C H P hCHeap hP hRoom hs).1

theorem height_budget {hCount3 : 3 = capacity.cap.value} (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount3).read j)) s)
    (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (K H P : ℕ) (hK : limits.heap.tape.length ≤ K) (hP : 0 < P) (hRoom : H < 2^P) :
    ReachableBudget (n := 3) (hCount := hCount3) seed limits hC
      (BinaryPRGHeapResourceThreeReservation.Reserved (hCount := hCount3) C s P H)
      (stepEnvelope K H capacity.width (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s)
        (BinaryThreeResourceHeight.coinWidth C s) seed.width seed.cap.value) := by
  refine ⟨?_,?_,?_⟩
  · intro state first second tail he pc hp h
    let choice := BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he
    have hHeap : state.heap.tape.length ≤ H := by have hh := h.2; omega
    have hActive := state.certified.choose_spec.2.symm.trans he
    have hFields := BinaryPRGWordControllerBooleanResourceThreeWork.source_height
      (hC := hC) C s state.reference hCap h.1 first second tail hActive
    have ht := (BinaryPRGWordControllerBooleanResourcePair.source capacity.tree state.reference.state
      first second tail hC state.reference.canonical state.reference.interior hActive).trace_wordBounds
      hFields (hs.trans (expressionHeightBudget_ge_input s _))
    have hTrace : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code
        (BinaryPRGHeapResourceLoop.sourceWithWork (hC := hC) limits state first second tail he).1.inputs
        (BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s) := by
      rw [BinaryPRGHeapResourceLoop.sourceWithWork_value]
      exact ht
    have hNativeWidth := BinaryThreeResourceHeight.probability_width C s hs hCap
      (BinaryPRGWordControllerBooleanResourceThreeBridge.choice_toThree choice.original).original h.1
    have hWord : choice.outputs.probability =
        (BinaryPRGWordControllerBooleanResourceThreeBridge.choice_toThree choice.original).original.probability :=
      (BinaryPRGWordControllerBooleanResourceLoop.Choice.probability_original choice).trans
        (BinaryPRGWordControllerThreeChoice.Choice.probability_original
          (BinaryPRGWordControllerBooleanResourceThreeBridge.choice_toThree choice.original))
    have hPhysical := congrArg (fun outputs : BinaryPRGWordControllerPairOutputs.Outputs => width outputs.probability)
      (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he)
    have hWidth := hPhysical.trans_le ((congrArg width hWord).le.trans hNativeWidth)
    exact pairCoin_usage seed limits state first second tail he pc hp K H _ _ hK hHeap hTrace hWidth
  · intro state first second tail he outputs hOutputs branch h
    exact (BinaryPRGHeapSelectedLifetime.select_height_usage C s hs hCap limits state h.1
      first second tail he outputs hOutputs branch K H P hK hP
      (BinaryPRGHeapResourceThreeReservation.reserved_room C s P H state h first second tail he) hRoom).trans
        (le_max_right _ _)
  · intro state first second tail he outputs hOutputs branch h
    rw [BinaryPRGHeapLoopLifetime.selectWithTrace_erasure]
    have hUpdate := BinaryPRGHeapResourceThreeStep.selectWithWork_bound C s hs hCap limits state h.1
      first second tail he outputs hOutputs branch K H P hK hP
      (BinaryPRGHeapResourceThreeReservation.reserved_room C s P H state h first second tail he) hRoom
    have hHeight := BinaryPRGHeapResourceThreeStep.selected_height C s hs hCap limits state h.1
      first second tail he outputs hOutputs branch
    have hProgress := BinaryPRGHeapResourceLoop.selectWithWork_progress limits state first second tail he outputs hOutputs branch
    exact ⟨hHeight,BinaryPRGHeapResourceThreeReservation.reserve_step h.2 hUpdate.1 hProgress⟩

end Blotto.BinaryPRGHeapLifetimeReservation
