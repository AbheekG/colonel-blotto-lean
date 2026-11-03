import Blotto.BinaryQuadraticResourceLoopLifetime
import Blotto.BinaryPRGWordControllerBooleanResourceThreeWork

/-! Rank-height specialization of the SAME complete Boolean resource phase
trace. Reflected three-resource inputs need no unit-lattice premise here.
Actual fields and reached selected-height invariants derive pair/update/coin
widths, and the source join includes input trees and final materialization.
Physical scalar/pointer/compiler interpretation and work-observer execution
remain separate from retained source list/reference slots and activations. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticResourceThreeLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourcePair BinaryPRGWordControllerBooleanResourceLoop
open BinaryQuadraticResourceStateLifetime BinaryQuadraticResourceLoopLifetime BinaryThreeResourceHeight
open BinaryPRGWordControllerBooleanResourceThreeWork (threeReference resource_height_tree resource_width_tree capacity_width_tree source_height)
set_option maxHeartbeats 1500000
variable {capacity : Store} {hCount : 3 = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

abbrev W (C s : ℕ) : ℕ := BinaryPRGWordControllerBooleanResourceThreeWork.widthBound C s

theorem choice_height_bounds (C s : ℕ) (hs : 2 ≤ s) (state : Certified capacity 3 hCount)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state))
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.state.active = first :: second :: tail) :
    cells (choiceWithTrace (hC := hC) state first second tail he).2 ≤ preparationBound capacity.width (W C s) ∧
      framePeak (choiceWithTrace (hC := hC) state first second tail he).2 ≤ preparationFrames capacity.width (W C s) := by
  have ht := (source capacity.tree state.state first second tail hC state.canonical state.interior he).trace_wordBounds
    (source_height C s state hCap h first second tail he) (hs.trans (expressionHeightBudget_ge_input s _))
  have hp := BinaryQuadraticResourcePairLifetime.outputsWithTrace_bounds _ _ ht
  have h0 := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds capacity.tree first.word
  have h1 := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds capacity.tree second.word
  have h2 := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds state.state.resource first.word
  have h3 := BinaryQuadraticResourcePairLifetime.lookupWithTrace_bounds state.state.resource second.word
  have f0 := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace capacity.tree first.word).2
  have f1 := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace capacity.tree second.word).2
  have f2 := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace state.state.resource first.word).2
  have f3 := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace state.state.resource second.word).2
  have fp := framePeak_under 2 (BinaryQuadraticResourcePairLifetime.outputsWithTrace
    (source capacity.tree state.state first second tail hC state.canonical state.interior he)).2
  unfold choiceWithTrace preparationBound preparationFrames W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound
  simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by omega,by omega⟩

theorem prepare_height_bounds (C s : ℕ) (hs : 2 ≤ s) (capacity : Store) (hCount : 3 = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity 3 hCount)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state)) :
    cells (prepareWithTrace capacity 3 hCount hC state).2 ≤ preparationBound capacity.width (W C s) + 8 ∧
      framePeak (prepareWithTrace capacity 3 hCount hC state).2 ≤ preparationFrames capacity.width (W C s) + 2 := by
  unfold prepareWithTrace
  split
  · rename_i first second tail he
    have hp := choice_height_bounds (hC := hC) C s hs state hCap h first second tail he
    have hf := framePeak_under 2 (choiceWithTrace (hC := hC) state first second tail he).2
    simp only [cells] at hp
    simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
    exact ⟨by omega,by omega⟩
  · simp [cells,listCells,arraySlots,framePeak]

theorem select_height_bounds (C s : ℕ) (hs : 2 ≤ s) (choice : Choice capacity 3 hCount hC)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference choice.state)) (branch : Bool) :
    cells (selectWithTrace choice branch).2 ≤ updateBound capacity.width (W C s) + 16 ∧
      framePeak (selectWithTrace choice branch).2 ≤ updateFrames capacity.width (W C s) + 2 := by
  let input := source capacity.tree choice.state.state choice.first choice.second choice.tail hC choice.state.canonical choice.state.interior choice.head_pair
  have hPair := source_height (hC := hC) C s choice.state hCap h choice.first choice.second choice.tail choice.head_pair
  have hWords := input.run_wordBounds hPair (hs.trans (expressionHeightBudget_ge_input s _))
  have hChosen : width (choice.endpoint branch) ≤ W C s := by
    rw [Choice.endpoint,choice.outputs_correct]
    unfold pair
    cases branch
    · rw [(BinaryPRGWordControllerPairOutputs.prepare_words input).1]; exact hWords 7
    · rw [(BinaryPRGWordControllerPairOutputs.prepare_words input).2.1]; exact hWords 8
  have ha := apply_native .add _ _ (choice.state.canonical choice.first).1 (choice.state.canonical choice.second).1
  have hTotal : width (BinaryQuadraticData.apply .add (lookup choice.state.state.resource choice.first.word)
      (lookup choice.state.state.resource choice.second.word)) ≤ W C s := by
    rw [ha]
    have hi : RationalHeight (value (lookup choice.state.state.resource choice.first.word)) (expressionHeightBudget (resourceHeight C s) 0) := by
      simpa only [expressionHeightBudget_zero] using resource_height_tree C s choice.state h choice.first
    have hj : RationalHeight (value (lookup choice.state.state.resource choice.second.word)) (expressionHeightBudget (resourceHeight C s) 0) := by
      simpa only [expressionHeightBudget_zero] using resource_height_tree C s choice.state h choice.second
    have hn := BinaryRationalOpcode.apply_height_width .add _ _ (choice.state.canonical choice.first).1 (choice.state.canonical choice.second).1 _ (hi.add_level hj)
    norm_num [expressionHeightBudget] at hn
    unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound
    omega
  have hNext := BinaryPRGWordControllerBooleanResourceThreeWork.selected_height C s hs choice hCap h branch
  have hOther : width (BinaryQuadraticData.apply .sub
      (BinaryQuadraticData.apply .add (lookup choice.state.state.resource choice.first.word)
        (lookup choice.state.state.resource choice.second.word)) (choice.endpoint branch)) ≤ W C s := by
    have hn := resource_width_tree C s (choice.select branch) hNext choice.second
    simpa only [Choice.select,BinaryPRGWordControllerBooleanResourceUpdate.update,lookup_write,ite_true] using hn
  have hp := BinaryQuadraticResourceStateLifetime.updateWithTrace_bounds capacity.tree choice.state.state
    choice.first choice.second choice.tail (choice.endpoint branch) (W C s) (by unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega)
    (resource_width_tree C s choice.state h) (capacity_width_tree C s hC hCap) hChosen hTotal hOther
  have hf := framePeak_under 2 (BinaryQuadraticResourceStateLifetime.updateWithTrace capacity.tree choice.state.state
    choice.first choice.second choice.tail (choice.endpoint branch)).2
  simp only [cells] at hp
  unfold selectWithTrace
  simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by omega,by omega⟩

def stepBound (C s w seedWidth N : ℕ) : ℕ := preparationBound w (W C s) + updateBound w (W C s) +
  BinaryWordCoinLifetime.sampleBound (W C s) seedWidth N + 80
def framesBound (C s w seedWidth N : ℕ) : ℕ := preparationFrames w (W C s) + updateFrames w (W C s) + N + 2*(W C s) + 2*seedWidth + 60

theorem run_height_bounds (C s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity : Store) (hCount : 3 = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity 3 hCount)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    cells (BinaryQuadraticResourceLoopLifetime.runWithTrace seed capacity 3 hCount hC state pc hp).2 ≤ (state.state.active.length+1)*stepBound C s capacity.width seed.width seed.cap.value ∧
      framePeak (BinaryQuadraticResourceLoopLifetime.runWithTrace seed capacity 3 hCount hC state pc hp).2 ≤ (state.state.active.length+1)*framesBound C s capacity.width seed.width seed.cap.value := by
  have hPre := prepare_height_bounds C s hs capacity hCount hC state hCap h
  have hFrameBase : framesBound C s capacity.width seed.width seed.cap.value ≤
      (state.state.active.length+1)*framesBound C s capacity.width seed.width seed.cap.value := Nat.le_mul_of_pos_left _ (by omega)
  unfold BinaryQuadraticResourceLoopLifetime.runWithTrace
  dsimp only
  cases hPrepared : (prepareWithTrace capacity 3 hCount hC state).1 with
  | done result =>
      have hf := framePeak_under 2 (prepareWithTrace capacity 3 hCount hC state).2
      simp only [cells] at hPre
      simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
      unfold stepBound
      unfold framesBound at hFrameBase ⊢
      exact ⟨by nlinarith only [hPre.1],by omega⟩
  | ask choice =>
      dsimp only
      have hw := prepared_state state choice ((prepareWithTrace_erases capacity 3 hCount hC state).symm.trans hPrepared)
      have hChoice : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference choice.state) := hw.symm ▸ h
      let input := source capacity.tree choice.state.state choice.first choice.second choice.tail hC choice.state.canonical choice.state.interior choice.head_pair
      have hPair := source_height (hC := hC) C s choice.state hCap hChoice choice.first choice.second choice.tail choice.head_pair
      have hWords := input.run_wordBounds hPair (hs.trans (expressionHeightBudget_ge_input s _))
      have hWidth : width choice.probability ≤ W C s := by
        rw [Choice.probability,choice.outputs_correct]
        unfold pair
        rw [(BinaryPRGWordControllerPairOutputs.prepare_words input).2.2]
        exact hWords 11
      have hCoin := BinaryWordCoinLifetime.sampleWithTrace_bounds seed choice.probability pc hp (W C s) hWidth
      have hCoinCap : cells (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).2 ≤
          BinaryWordCoinLifetime.sampleBound (W C s) seed.width seed.cap.value := by
        apply hCoin.1.trans
        unfold BinaryWordCoinLifetime.sampleBound
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)) _
      have pf := framePeak_under 2 (prepareWithTrace capacity 3 hCount hC state).2
      have cf := framePeak_under 2 (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).2
      cases hcoin : (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).1.1 with
      | none =>
          simp only [cells] at hPre hCoinCap
          simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
          unfold stepBound
          unfold framesBound at hFrameBase ⊢
          exact ⟨by nlinarith only [hPre.1,hCoinCap],by omega⟩
      | some branch =>
          dsimp only
          have hSelect := select_height_bounds C s hs choice hCap hChoice branch
          have hNext := BinaryPRGWordControllerBooleanResourceThreeWork.selected_height C s hs choice hCap hChoice branch
          rw [← selectWithTrace_erases] at hNext
          have ih := run_height_bounds C s hs seed capacity hCount hC (selectWithTrace choice branch).1 hCap hNext
            (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).1.2 (BinaryWordCoinLifetime.sampleWithTrace_position seed choice.probability pc hp).2
          have hLength := choice.select_progress branch
          rw [hw,← selectWithTrace_erases] at hLength
          have sf := framePeak_under 2 (selectWithTrace choice branch).2
          have lf := framePeak_under 1 (BinaryQuadraticResourceLoopLifetime.runWithTrace seed capacity 3 hCount hC (selectWithTrace choice branch).1
            (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).1.2 (BinaryWordCoinLifetime.sampleWithTrace_position seed choice.probability pc hp).2).2
          simp only [cells] at hPre hCoinCap hSelect ih
          have hFramePos : 4 ≤ framesBound C s capacity.width seed.width seed.cap.value := by unfold framesBound; omega
          have hRanks : (selectWithTrace choice branch).1.state.active.length+1 ≤ state.state.active.length := by omega
          have hRanksFrames := Nat.mul_le_mul_right (framesBound C s capacity.width seed.width seed.cap.value) hRanks
          have hLaterFrames : framePeak (under 1 (BinaryQuadraticResourceLoopLifetime.runWithTrace seed capacity 3 hCount hC (selectWithTrace choice branch).1
              (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).1.2 (BinaryWordCoinLifetime.sampleWithTrace_position seed choice.probability pc hp).2).2) ≤
              (state.state.active.length+1)*framesBound C s capacity.width seed.width seed.cap.value := by
            nlinarith only [lf,ih.2,hRanksFrames,hFramePos]
          simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
          have hIHCells := ih.1
          unfold stepBound at hIHCells ⊢
          unfold framesBound at hFrameBase hLaterFrames ⊢
          exact ⟨by nlinarith only [hPre.1,hCoinCap,hSelect.1,hIHCells,hLength],by omega⟩
termination_by state.state.active.length
decreasing_by
  rw [selectWithTrace_erases]
  have hw := prepared_state state choice ((prepareWithTrace_erases capacity 3 hCount hC state).symm.trans hPrepared)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

def sourceAtWithTrace (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    BinaryPRGWordControllerResource.Result seed capacity × Trace :=
  let started := BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace capacity resource hC hR
  let drawn := BinaryQuadraticResourceLoopLifetime.runWithTrace seed (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity) 3
    (BinaryPRGWordControllerBooleanResourceSource.source_count capacity)
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) started.1 pc hp
  match drawn.1.1 with
  | none => ((none,drawn.1.2),[.frames 2,.arrayAllocation 24] ++ under 2 started.2 ++ under 2 drawn.2)
  | some state =>
      let output := BinaryQuadraticResourceSourceLifetime.materializeWithTrace capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity) state
      ((some output.1,drawn.1.2),[.frames 2,.arrayAllocation 24] ++ under 2 started.2 ++ under 2 drawn.2 ++ under 2 output.2)

@[simp] theorem sourceAtWithTrace_erases (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceAtWithTrace seed capacity resource hC hR pc hp).1 =
      (BinaryPRGWordControllerBooleanResourceSourceWork.initialAt seed capacity resource hC hR pc hp).1 := by
  unfold sourceAtWithTrace BinaryPRGWordControllerBooleanResourceSourceWork.initialAt
  dsimp only
  rw [BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace_erases,BinaryQuadraticResourceLoopLifetime.runWithTrace_erases,
    BinaryPRGWordControllerBooleanResourceLoopWork.run_erasure,BinaryPRGWordControllerBooleanResourceSourceWork.prepare_state,
    BinaryPRGWordControllerBooleanResourceSourceWork.initialWithWork_erasure]
  dsimp only [BinaryPRGWordControllerBooleanResourceSourceWork.prepare]
  cases hr : (BinaryPRGWordControllerBooleanResourceLoop.run seed (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity) 3
      (BinaryPRGWordControllerBooleanResourceSource.source_count capacity)
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      (BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR) pc hp).1 with
  | none => rfl
  | some state =>
      dsimp only
      rw [BinaryQuadraticResourceSourceLifetime.materializeWithTrace_erases]
      apply Prod.ext
      · apply congrArg some
        exact (BinaryPRGWordControllerBooleanResourceSourceWork.materializeWithWork_erasure capacity
          (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity) state).symm
      · rfl

def sourceBound (s w seedWidth N : ℕ) : ℕ :=
  BinaryQuadraticResourceSourceLifetime.startBound 3 w (W 2 s) + 4*stepBound 2 s w seedWidth N +
    BinaryQuadraticResourceSourceLifetime.outputBound 3 w + seedWidth + 24
def sourceFrames (s w seedWidth N : ℕ) : ℕ :=
  BinaryQuadraticResourceSourceLifetime.startFrames 3 w (W 2 s) + 4*framesBound 2 s w seedWidth N +
    BinaryQuadraticResourceSourceLifetime.outputFrames 3 w + seedWidth + 10

theorem source_height_bounds (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCap : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    cells (sourceRunWithTrace seed capacity resource hC hR).2 ≤
      sourceBound s (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value ∧
    framePeak (sourceRunWithTrace seed capacity resource hC hR).2 ≤
      sourceFrames s (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value := by
  let cached := BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity
  let hCount := BinaryPRGWordControllerBooleanResourceSource.source_count capacity
  let hc := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC
  let started := BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace capacity resource hC hR
  have hCapWord : ∀ j,width (capacity.read j) ≤ W 2 s := by
    intro j
    have hv := (hC j).2.trans (rationalWordWidth_of_height ((hCap j).mono (expressionHeightBudget_ge_input s (3*2))))
    unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound resourceHeight
    omega
  have hResWord : ∀ j,width (resource.read j) ≤ W 2 s := by
    intro j
    have hv := (hR j).2.trans (rationalWordWidth_of_height ((hResource j).mono (expressionHeightBudget_ge_input s (3*2))))
    unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound resourceHeight
    omega
  have hCapTree : ∀ address : Address cached.width cached.cap,width (lookup cached.tree address.word) ≤ W 2 s := by
    intro address
    have hRead := table_read cached.tree address 3 hCount
    have hTable := congrArg (fun t : FixedArrayTable 3 SignedWord => t.read (address.index 3 hCount))
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    rw [← hRead,hTable]
    exact hCapWord _
  have hResTree : ∀ address : Address cached.width cached.cap,
      width (lookup (BinaryPRGWordControllerBooleanResourceSource.resourceStore capacity resource).tree address.word) ≤ W 2 s := by
    intro address
    have hRead := table_read (BinaryPRGWordControllerBooleanResourceSource.resourceStore capacity resource).tree address 3 hCount
    have hTable := congrArg (fun t : FixedArrayTable 3 SignedWord => t.read (address.index 3 hCount))
      (BinaryPRGWordControllerBooleanResourceSource.resourceTable capacity resource)
    exact (hTable.symm.trans hRead) ▸ hResWord (address.index 3 hCount)
  have hStart := BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace_bounds capacity resource hC hR (W 2 s)
    (by unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega) hCapTree hResTree
  have hState : StateHeight (table cached.cap cached.tree 3 hCount) 2 s (threeReference started.1) := by
    rw [BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace_erases]
    exact BinaryPRGWordControllerBooleanResourceThreeWork.source_initial_height capacity resource hC hR s hResource
  have hCapHeight : ∀ j,RationalHeight (value ((table cached.cap cached.tree 3 hCount).read j)) s := by
    intro j
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hCap j
  let drawn := BinaryQuadraticResourceLoopLifetime.runWithTrace seed cached 3 hCount hc started.1 (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  have hRun := run_height_bounds 2 s hs seed cached hCount hc started.1 hCapHeight hState
    (BinaryWordIndexCoinController.zeroIndex seed) (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  have hActive := BinaryGeneralResourceRun.active_length_le started.1.reference
  rw [started.1.reference_state] at hActive
  simp only [State.reference,List.length_map] at hActive
  have hRunCells : cells drawn.2 ≤ 4*stepBound 2 s cached.width seed.width seed.cap.value :=
    hRun.1.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hActive 1))
  have hRunFrames : framePeak drawn.2 ≤ 4*framesBound 2 s cached.width seed.width seed.cap.value :=
    hRun.2.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hActive 1))
  have sf := framePeak_under 2 started.2
  have rf := framePeak_under 2 drawn.2
  simp only [cells] at hStart hRunCells
  unfold sourceRunWithTrace
  dsimp only
  cases hResult : drawn.1.1 with
  | none =>
      dsimp only [drawn,cached,hCount,hc,started] at hResult
      simp only [hResult]
      unfold sourceBound sourceFrames
      simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
      dsimp only [cached,started,drawn] at hStart hRunCells hRunFrames sf rf ⊢
      exact ⟨by omega,by omega⟩
  | some finished =>
      dsimp only [drawn,cached,hCount,hc,started] at hResult
      simp only [hResult]
      have hOutput := BinaryQuadraticResourceSourceLifetime.materializeWithTrace_bounds capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity) finished
      have ofr := framePeak_under 2 (BinaryQuadraticResourceSourceLifetime.materializeWithTrace capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity) finished).2
      simp only [cells] at hOutput
      unfold sourceBound sourceFrames
      simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
      dsimp only [cached,started,drawn] at hStart hRunCells hRunFrames sf rf ⊢
      exact ⟨by omega,by omega⟩

theorem sourceAt_height_bounds (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCap : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    cells (sourceAtWithTrace seed capacity resource hC hR pc hp).2 ≤
      sourceBound s (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value ∧
    framePeak (sourceAtWithTrace seed capacity resource hC hR pc hp).2 ≤
      sourceFrames s (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value := by
  let cached := BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity
  let hCount := BinaryPRGWordControllerBooleanResourceSource.source_count capacity
  let hc := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC
  let started := BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace capacity resource hC hR
  have hCapWord : ∀ j,width (capacity.read j) ≤ W 2 s := by
    intro j
    have hv := (hC j).2.trans (rationalWordWidth_of_height ((hCap j).mono (expressionHeightBudget_ge_input s (3*2))))
    unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound resourceHeight
    omega
  have hResWord : ∀ j,width (resource.read j) ≤ W 2 s := by
    intro j
    have hv := (hR j).2.trans (rationalWordWidth_of_height ((hResource j).mono (expressionHeightBudget_ge_input s (3*2))))
    unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound resourceHeight
    omega
  have hCapTree : ∀ address : Address cached.width cached.cap,width (lookup cached.tree address.word) ≤ W 2 s := by
    intro address
    have hRead := table_read cached.tree address 3 hCount
    have hTable := congrArg (fun t : FixedArrayTable 3 SignedWord => t.read (address.index 3 hCount))
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    rw [← hRead,hTable]
    exact hCapWord _
  have hResTree : ∀ address : Address cached.width cached.cap,
      width (lookup (BinaryPRGWordControllerBooleanResourceSource.resourceStore capacity resource).tree address.word) ≤ W 2 s := by
    intro address
    have hRead := table_read (BinaryPRGWordControllerBooleanResourceSource.resourceStore capacity resource).tree address 3 hCount
    have hTable := congrArg (fun t : FixedArrayTable 3 SignedWord => t.read (address.index 3 hCount))
      (BinaryPRGWordControllerBooleanResourceSource.resourceTable capacity resource)
    exact (hTable.symm.trans hRead) ▸ hResWord (address.index 3 hCount)
  have hStart := BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace_bounds capacity resource hC hR (W 2 s)
    (by unfold W BinaryPRGWordControllerBooleanResourceThreeWork.widthBound; omega) hCapTree hResTree
  have hState : StateHeight (table cached.cap cached.tree 3 hCount) 2 s (threeReference started.1) := by
    rw [BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace_erases]
    exact BinaryPRGWordControllerBooleanResourceThreeWork.source_initial_height capacity resource hC hR s hResource
  have hCapHeight : ∀ j,RationalHeight (value ((table cached.cap cached.tree 3 hCount).read j)) s := by
    intro j
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hCap j
  let drawn := BinaryQuadraticResourceLoopLifetime.runWithTrace seed cached 3 hCount hc started.1 pc hp
  have hRun := run_height_bounds 2 s hs seed cached hCount hc started.1 hCapHeight hState
    pc hp
  have hActive := BinaryGeneralResourceRun.active_length_le started.1.reference
  rw [started.1.reference_state] at hActive
  simp only [State.reference,List.length_map] at hActive
  have hRunCells : cells drawn.2 ≤ 4*stepBound 2 s cached.width seed.width seed.cap.value :=
    hRun.1.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hActive 1))
  have hRunFrames : framePeak drawn.2 ≤ 4*framesBound 2 s cached.width seed.width seed.cap.value :=
    hRun.2.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hActive 1))
  have sf := framePeak_under 2 started.2
  have rf := framePeak_under 2 drawn.2
  simp only [cells] at hStart hRunCells
  unfold sourceAtWithTrace
  dsimp only
  cases hResult : drawn.1.1 with
  | none =>
      dsimp only [drawn,cached,hCount,hc,started] at hResult
      simp only [hResult]
      unfold sourceBound sourceFrames
      simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
      dsimp only [cached,started,drawn] at hStart hRunCells hRunFrames sf rf ⊢
      exact ⟨by omega,by omega⟩
  | some finished =>
      dsimp only [drawn,cached,hCount,hc,started] at hResult
      simp only [hResult]
      have hOutput := BinaryQuadraticResourceSourceLifetime.materializeWithTrace_bounds capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity) finished
      have ofr := framePeak_under 2 (BinaryQuadraticResourceSourceLifetime.materializeWithTrace capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity) finished).2
      simp only [cells] at hOutput
      unfold sourceBound sourceFrames
      simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
      dsimp only [cached,started,drawn] at hStart hRunCells hRunFrames sf rf ⊢
      exact ⟨by omega,by omega⟩

theorem source_all_prefix_heap (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCap : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (inputCells capacity resource + BinaryWordStoreLifetime.storeCells seed + originalSeedCells + borrowedOtherCells)
      (sourceRunWithTrace seed capacity resource hC hR).2 steps ≤
      inputCells capacity resource + BinaryWordStoreLifetime.storeCells seed + originalSeedCells + borrowedOtherCells +
        sourceBound s (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (source_height_bounds s hs seed capacity resource hC hR hCap hResource).1

theorem source_all_prefix_frames (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCap : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s) (steps : ℕ) :
    framePeak ((sourceRunWithTrace seed capacity resource hC hR).2.take steps) ≤
      sourceFrames s (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value :=
  (framePeak_take_le _ _).trans (source_height_bounds s hs seed capacity resource hC hR hCap hResource).2

theorem sourceAt_all_prefix_heap (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCap : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (inputCells capacity resource + BinaryWordStoreLifetime.storeCells seed + pc.bits.length + originalSeedCells + borrowedOtherCells)
      (sourceAtWithTrace seed capacity resource hC hR pc hp).2 steps ≤
      inputCells capacity resource + BinaryWordStoreLifetime.storeCells seed + pc.bits.length + originalSeedCells + borrowedOtherCells +
        sourceBound s (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (sourceAt_height_bounds s hs seed capacity resource hC hR hCap hResource pc hp).1

theorem sourceAt_all_prefix_frames (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCap : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (steps : ℕ) :
    framePeak ((sourceAtWithTrace seed capacity resource hC hR pc hp).2.take steps) ≤
      sourceFrames s (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value :=
  (framePeak_take_le _ _).trans (sourceAt_height_bounds s hs seed capacity resource hC hR hCap hResource pc hp).2

end Blotto.BinaryQuadraticResourceThreeLifetime
