import Blotto.BinaryPRGWordControllerBooleanResourceThreeBridge
import Blotto.BinaryThreeResourceHeight

/-! Rank-derived prices for the same Boolean outer resource program at three
coordinates. Existing native three-state heights are proof-only invariants;
actual pair preparation, selected path-copy writes/scans and shared-cap coins
remain the Boolean program. Source preparation/materialization joins follow. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourceThreeWork
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourcePair BinaryPRGWordControllerBooleanResourceLoop
open BinaryPRGWordControllerBooleanResourceThreeBridge BinaryThreeResourceHeight
open BinaryPRGWordControllerBooleanResourceLoopWork (prepareWithWork prepareWithWork_erasure selectWithWork selectWithWork_erasure)
variable {capacity : Store} {hCount : 3 = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
set_option maxHeartbeats 1000000

noncomputable def threeReference (state : Certified capacity 3 hCount) :
    BinaryThreeResourcePair.Certified (table capacity.cap capacity.tree 3 hCount) := generalCertified_toThree state.reference

def widthBound (C s : ℕ) : ℕ := 32 * resourceHeight C s + 31

theorem resource_height_tree (C s : ℕ) (state : Certified capacity 3 hCount)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state))
    (address : Address capacity.width capacity.cap) : RationalHeight (value (lookup state.state.resource address.word)) (resourceHeight C s) := by
  have hNative := resource_height C s (threeReference state) h (address.index 3 hCount)
  simp only [threeReference,generalCertified_toThree,generalState_toThree,Certified.reference_state,State.reference,table_read] at hNative
  exact hNative

theorem resource_width_tree (C s : ℕ) (state : Certified capacity 3 hCount)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state))
    (address : Address capacity.width capacity.cap) : width (lookup state.state.resource address.word) ≤ widthBound C s := by
  have hn := (state.canonical address).2.trans (rationalWordWidth_of_height (resource_height_tree C s state h address))
  unfold widthBound
  omega

theorem capacity_width_tree (C s : ℕ)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (address : Address capacity.width capacity.cap) : width (lookup capacity.tree address.word) ≤ widthBound C s := by
  have hn := capacity_height (table capacity.cap capacity.tree 3 hCount) C s hCap (address.index 3 hCount)
  rw [table_read] at hn
  have h := (hC address).2.trans (rationalWordWidth_of_height hn)
  unfold widthBound
  omega

theorem source_height (C s : ℕ) (state : Certified capacity 3 hCount)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state))
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.state.active = first :: second :: tail) :
    (source capacity.tree state.state first second tail hC state.canonical state.interior he).pair.FieldsHeight (resourceHeight C s) := by
  have hi := capacity_height (table capacity.cap capacity.tree 3 hCount) C s hCap (first.index 3 hCount)
  have hj := capacity_height (table capacity.cap capacity.tree 3 hCount) C s hCap (second.index 3 hCount)
  rw [table_read] at hi hj
  exact ⟨hi,hj,resource_height_tree C s state h first,resource_height_tree C s state h second⟩

theorem prepareWithWork_bound (C s : ℕ) (hs : 2 ≤ s) (capacity : Store) (hCount : 3 = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity 3 hCount)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state)) :
    (prepareWithWork capacity 3 hCount hC state).2 ≤ BinaryPRGWordControllerBooleanResourcePair.bound capacity.width (widthBound C s) + 1 := by
  unfold BinaryPRGWordControllerBooleanResourceLoopWork.prepareWithWork
  split
  · rename_i first second tail he
    have ht := (source capacity.tree state.state first second tail hC state.canonical state.interior he).trace_wordBounds
      (source_height C s state hCap h first second tail he) (hs.trans (expressionHeightBudget_ge_input s _))
    exact Nat.add_le_add_right (pairWithWork_bound capacity.tree state.state first second tail hC state.canonical state.interior he (widthBound C s) ht) 1
  · omega

theorem selected_height (C s : ℕ) (hs : 2 ≤ s) (choice : Choice capacity 3 hCount hC)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference choice.state)) (branch : Bool) :
    StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference (choice.select branch)) := by
  have hn := BinaryThreeResourceHeight.selected_height C s hs hCap (choice_toThree choice.original).original h branch
  rw [← BinaryPRGWordControllerThreeChoice.Choice.select_original,choice_toThree_select,← choice.select_original] at hn
  exact hn

theorem selectWithWork_bound (C s : ℕ) (hs : 2 ≤ s) (choice : Choice capacity 3 hCount hC)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference choice.state)) (branch : Bool) :
    (selectWithWork choice branch).2 ≤ BinaryPRGWordControllerBooleanResourceUpdateWork.updateBound capacity.width (widthBound C s) 3 := by
  let input := source capacity.tree choice.state.state choice.first choice.second choice.tail hC choice.state.canonical choice.state.interior choice.head_pair
  have hPair := source_height (hC := hC) C s choice.state hCap h choice.first choice.second choice.tail choice.head_pair
  have hsH := hs.trans (expressionHeightBudget_ge_input s (3 * C))
  have hWords := input.run_wordBounds hPair hsH
  have hChosen : width (choice.endpoint branch) ≤ widthBound C s := by
    rw [Choice.endpoint,choice.outputs_correct]
    unfold pair
    cases branch
    · rw [(BinaryPRGWordControllerPairOutputs.prepare_words input).1]
      exact hWords 7
    · rw [(BinaryPRGWordControllerPairOutputs.prepare_words input).2.1]
      exact hWords 8
  have hFirst := (choice.state.canonical choice.first).1
  have hSecond := (choice.state.canonical choice.second).1
  have ha := apply_native .add _ _ hFirst hSecond
  have hTotal : width (BinaryQuadraticData.apply .add (lookup choice.state.state.resource choice.first.word)
      (lookup choice.state.state.resource choice.second.word)) ≤ widthBound C s := by
    rw [ha]
    have hi : RationalHeight (value (lookup choice.state.state.resource choice.first.word)) (expressionHeightBudget (resourceHeight C s) 0) := by
      simpa only [expressionHeightBudget_zero] using resource_height_tree C s choice.state h choice.first
    have hj : RationalHeight (value (lookup choice.state.state.resource choice.second.word)) (expressionHeightBudget (resourceHeight C s) 0) := by
      simpa only [expressionHeightBudget_zero] using resource_height_tree C s choice.state h choice.second
    have hn := BinaryRationalOpcode.apply_height_width .add _ _ hFirst hSecond _ (hi.add_level hj)
    norm_num [expressionHeightBudget] at hn
    unfold widthBound
    omega
  have hNext := selected_height C s hs choice hCap h branch
  have hOther : width (BinaryQuadraticData.apply .sub
      (BinaryQuadraticData.apply .add (lookup choice.state.state.resource choice.first.word)
        (lookup choice.state.state.resource choice.second.word)) (choice.endpoint branch)) ≤ widthBound C s := by
    have hn := resource_width_tree C s (choice.select branch) hNext choice.second
    simpa only [Choice.select,BinaryPRGWordControllerBooleanResourceUpdate.update,lookup_write,ite_true] using hn
  have hUpdate := BinaryPRGWordControllerBooleanResourceUpdateWork.updateWithWork_bound capacity.tree choice.state.state
    choice.first choice.second choice.tail (choice.endpoint branch) (widthBound C s) (by unfold widthBound; omega)
    (resource_width_tree C s choice.state h) (capacity_width_tree C s hC hCap) hChosen hTotal hOther
  have hLength : choice.tail.length ≤ 3 := by
    have hn := BinaryGeneralResourceRun.active_length_le choice.state.reference
    rw [choice.state.reference_state] at hn
    simp only [State.reference,List.length_map,choice.head_pair,List.length_cons] at hn
    omega
  exact hUpdate.trans (by unfold BinaryPRGWordControllerBooleanResourceUpdateWork.updateBound; nlinarith)

def pairBound (C s resourceIndexWidth seedIndexWidth : ℕ) : ℕ :=
  BinaryPRGWordControllerBooleanResourcePair.bound resourceIndexWidth (widthBound C s) + 1 +
    BinaryPRGWordControllerBooleanResourceUpdateWork.updateBound resourceIndexWidth (widthBound C s) 3 +
      12 * (coinWidth C s + 1) + BinaryPRGWordControllerThreeResource.bodyBound C s seedIndexWidth + 2

def bound (C s resourceIndexWidth seedIndexWidth active span : ℕ) : ℕ :=
  (active + 1) * pairBound C s resourceIndexWidth seedIndexWidth + span * BinaryPRGWordControllerThreeResource.bodyBound C s seedIndexWidth

theorem run_bound (C s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity : Store) (hCount : 3 = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity 3 hCount)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerBooleanResourceLoopWork.run seed capacity 3 hCount hC state pc hp).2 ≤
      bound C s capacity.width seed.width state.state.active.length
        ((BinaryPRGWordControllerBooleanResourceLoopWork.run seed capacity 3 hCount hC state pc hp).1.2.value - pc.value) := by
  have hPreparation := prepareWithWork_bound C s hs capacity hCount hC state hCap h
  conv_lhs => unfold BinaryPRGWordControllerBooleanResourceLoopWork.run
  conv_rhs => arg 6; arg 1; arg 1; unfold BinaryPRGWordControllerBooleanResourceLoopWork.run
  dsimp only
  cases hPrepared : (prepareWithWork capacity 3 hCount hC state).1 with
  | done result => simp only [Nat.sub_self]; unfold bound pairBound; nlinarith
  | ask choice =>
      dsimp only
      have hw := prepared_state state choice ((prepareWithWork_erasure capacity 3 hCount hC state).symm.trans hPrepared)
      have hChoice : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference choice.state) := hw.symm ▸ h
      have hCoin := BinaryPRGWordControllerThreeResource.coin_bound C s hs seed (choice_toThree choice.original) hCap hChoice pc hp
      rw [choice_toThree_probability,← choice.probability_original] at hCoin
      have hPosition := BinaryWordIndexCoinController.sample_position_bounds seed choice.probability pc hp
      cases hcoin : (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.1 with
      | none => dsimp only; unfold bound pairBound; nlinarith
      | some branch =>
          dsimp only
          have hSelect := selectWithWork_bound C s hs choice hCap hChoice branch
          have hNext := selected_height C s hs choice hCap hChoice branch
          rw [← selectWithWork_erasure] at hNext
          have ih := run_bound C s hs seed capacity hCount hC (selectWithWork choice branch).1 hCap hNext
            (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2 hPosition.2
          have hLength := choice.select_progress branch
          rw [hw,← selectWithWork_erasure] at hLength
          have hLaterPosition := BinaryPRGWordControllerBooleanResourceLoop.run_position seed capacity 3 hCount hC
            (selectWithWork choice branch).1 (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2 hPosition.2
          rw [← BinaryPRGWordControllerBooleanResourceLoopWork.run_erasure] at hLaterPosition
          have hSpan :
            (BinaryPRGWordControllerBooleanResourceLoopWork.run seed capacity 3 hCount hC (selectWithWork choice branch).1
              (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2 hPosition.2).1.2.value - pc.value =
              ((BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2.value - pc.value) +
              ((BinaryPRGWordControllerBooleanResourceLoopWork.run seed capacity 3 hCount hC (selectWithWork choice branch).1
                (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2 hPosition.2).1.2.value -
                  (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2.value) := by omega
          rw [hSpan]
          unfold bound pairBound at ih ⊢
          nlinarith
termination_by state.state.active.length
decreasing_by
  rw [selectWithWork_erasure]
  have hw := prepared_state state choice ((prepareWithWork_erasure capacity 3 hCount hC state).symm.trans hPrepared)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_completed_height (C s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (capacity : Store) (hCount : 3 = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity 3 hCount)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (h : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference state))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (result : Certified capacity 3 hCount)
    (hSuccess : (BinaryPRGWordControllerBooleanResourceLoopWork.run seed capacity 3 hCount hC state pc hp).1.1 = some result) :
    StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference result) := by
  unfold BinaryPRGWordControllerBooleanResourceLoopWork.run at hSuccess
  dsimp only at hSuccess
  split at hSuccess
  · rename_i finished hPrepared
    cases hSuccess
    have he := prepared_done_state state result ((prepareWithWork_erasure capacity 3 hCount hC state).symm.trans hPrepared)
    rw [he]
    exact h
  · rename_i choice hPrepared
    have hw := prepared_state state choice ((prepareWithWork_erasure capacity 3 hCount hC state).symm.trans hPrepared)
    have hChoice : StateHeight (table capacity.cap capacity.tree 3 hCount) C s (threeReference choice.state) := hw.symm ▸ h
    split at hSuccess
    · cases hSuccess
    · rename_i branch hCoin
      have hNext := selected_height C s hs choice hCap hChoice branch
      rw [← selectWithWork_erasure] at hNext
      exact run_completed_height C s hs seed capacity hCount hC (selectWithWork choice branch).1 hCap hNext
        (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2
        (BinaryWordIndexCoinController.sample_position_bounds seed choice.probability pc hp).2 result hSuccess
termination_by state.state.active.length
decreasing_by
  rw [selectWithWork_erasure]
  have hw := prepared_state state _ ((prepareWithWork_erasure capacity 3 hCount hC state).symm.trans (by assumption))
  rw [← hw]
  exact Choice.select_progress _ _

open BinaryPRGWordControllerBooleanResourceSource

theorem height_transport {first second : FixedArrayTable 3 SignedWord} (h : first = second)
    (C s : ℕ) (state : BinaryResourcePair.Certified first) :
    StateHeight second C s (generalCertified_toThree (transport h state)) =
      StateHeight first C s (generalCertified_toThree state) := by
  subst second
  rfl

theorem source_initial_height (nativeCapacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (s : ℕ) (hResource : ∀ j,RationalHeight (value (resource.read j)) s) :
    StateHeight (table (capacityStore nativeCapacity).cap (capacityStore nativeCapacity).tree 3 (source_count nativeCapacity))
      2 s (threeReference (BinaryPRGWordControllerBooleanResourceSource.initial nativeCapacity resource hC hR)) := by
  unfold threeReference
  rw [← height_transport (capacityTable nativeCapacity) 2 s _,
    BinaryPRGWordControllerBooleanResourceSource.initial_reference,general_toThree_initial]
  exact BinaryThreeResourceHeight.initial_height nativeCapacity resource hC hR s hResource

def sourceEnvelope (s resourceIndexWidth seedIndexWidth span : ℕ) : ℕ :=
  BinaryPRGWordControllerBooleanResourceSourceWork.inputBound 3 (widthBound 2 s) +
    BinaryPRGWordControllerBooleanResourceInitial.initialBound resourceIndexWidth (widthBound 2 s) 3 +
      bound 2 s resourceIndexWidth seedIndexWidth 3 span +
        BinaryPRGWordControllerBooleanResourceSourceWork.outputBound 3 resourceIndexWidth (widthBound 2 s) + 6

theorem source_initialAt_bound (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (nativeCapacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCap : ∀ j,RationalHeight (value (nativeCapacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerBooleanResourceSourceWork.initialAt seed nativeCapacity resource hC hR pc hp).2 + 4 ≤
      sourceEnvelope s (capacityStore nativeCapacity).width seed.width (seed.cap.value - pc.value) := by
  let W := widthBound 2 s
  have hW : 1 ≤ W := by dsimp [W,widthBound]; omega
  have hcWidth : ∀ j,width (nativeCapacity.read j) ≤ W := by
    intro j
    have hn := (hC j).2.trans (rationalWordWidth_of_height ((hCap j).mono (expressionHeightBudget_ge_input s 6)))
    dsimp [W,widthBound,resourceHeight]
    omega
  have hrWidth : ∀ j,width (resource.read j) ≤ W := by
    intro j
    have hn := (hR j).2.trans (rationalWordWidth_of_height ((hResource j).mono (expressionHeightBudget_ge_input s 6)))
    dsimp [W,widthBound,resourceHeight]
    omega
  have hInput := BinaryPRGWordControllerBooleanResourceSourceWork.inputWork_bound nativeCapacity resource W hW hcWidth hrWidth
  have hCapTree : ∀ address : Address (capacityStore nativeCapacity).width (capacityStore nativeCapacity).cap,
      width (lookup (capacityStore nativeCapacity).tree address.word) ≤ W := by
    intro address
    have hRead := table_read (capacityStore nativeCapacity).tree address 3 (source_count nativeCapacity)
    have hTable := congrArg (fun t : FixedArrayTable 3 SignedWord => t.read (address.index 3 (source_count nativeCapacity))) (capacityTable nativeCapacity)
    exact (hTable.symm.trans hRead) ▸ hcWidth (address.index 3 (source_count nativeCapacity))
  have hResTree : ∀ address : Address (capacityStore nativeCapacity).width (capacityStore nativeCapacity).cap,
      width (lookup (resourceStore nativeCapacity resource).tree address.word) ≤ W := by
    intro address
    have hRead := table_read (resourceStore nativeCapacity resource).tree address 3 (source_count nativeCapacity)
    have hTable := congrArg (fun t : FixedArrayTable 3 SignedWord => t.read (address.index 3 (source_count nativeCapacity))) (resourceTable nativeCapacity resource)
    exact (hTable.symm.trans hRead) ▸ hrWidth (address.index 3 (source_count nativeCapacity))
  have hStart := BinaryPRGWordControllerBooleanResourceInitial.initialWithWork_bound
    (capacityStore nativeCapacity) (resourceStore nativeCapacity resource) rfl rfl W hW hCapTree hResTree
  rw [← source_count nativeCapacity] at hStart
  let started := BinaryPRGWordControllerBooleanResourceSourceWork.prepare nativeCapacity resource hC hR
  have hPreparedWork : started.work ≤ BinaryPRGWordControllerBooleanResourceSourceWork.inputBound 3 W +
      BinaryPRGWordControllerBooleanResourceInitial.initialBound started.cached.width W 3 :=
    Nat.add_le_add hInput hStart
  have hCapTreeHeight : ∀ j,RationalHeight (value ((table started.cached.cap started.cached.tree 3 started.count).read j)) s := by
    intro j
    change RationalHeight (value ((table (capacityStore nativeCapacity).cap (capacityStore nativeCapacity).tree 3 (source_count nativeCapacity)).read j)) s
    rw [capacityTable]
    exact hCap j
  have hInitial : StateHeight (table started.cached.cap started.cached.tree 3 started.count) 2 s (threeReference started.state) := by
    rw [BinaryPRGWordControllerBooleanResourceSourceWork.prepare_state,BinaryPRGWordControllerBooleanResourceSourceWork.initialWithWork_erasure]
    exact source_initial_height nativeCapacity resource hC hR s hResource
  have hRun := run_bound 2 s hs seed started.cached started.count started.canonical started.state hCapTreeHeight hInitial pc hp
  have hActive := BinaryGeneralResourceRun.active_length_le started.state.reference
  rw [Certified.reference_state] at hActive
  simp only [State.reference,List.length_map] at hActive
  have hPosition := BinaryPRGWordControllerBooleanResourceLoop.run_position seed started.cached 3 started.count started.canonical started.state pc hp
  rw [← BinaryPRGWordControllerBooleanResourceLoopWork.run_erasure] at hPosition
  have hRunCap : (BinaryPRGWordControllerBooleanResourceLoopWork.run seed started.cached 3 started.count started.canonical started.state pc hp).2 ≤
      bound 2 s started.cached.width seed.width 3 (seed.cap.value - pc.value) := by
    apply hRun.trans
    unfold bound
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.add_le_add_right hActive 1))
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hPosition.2 pc.value))
  unfold BinaryPRGWordControllerBooleanResourceSourceWork.initialAt
  dsimp only
  split
  · unfold sourceEnvelope
    change started.work + _ + 2 + 4 ≤ BinaryPRGWordControllerBooleanResourceSourceWork.inputBound 3 W +
      BinaryPRGWordControllerBooleanResourceInitial.initialBound started.cached.width W 3 +
        bound 2 s started.cached.width seed.width 3 (seed.cap.value - pc.value) +
          BinaryPRGWordControllerBooleanResourceSourceWork.outputBound 3 started.cached.width W + 6
    dsimp only [started] at hRunCap hPreparedWork ⊢
    omega
  · rename_i finished hSuccess
    have hFinal := run_completed_height 2 s hs seed started.cached started.count started.canonical started.state
      hCapTreeHeight hInitial pc hp finished hSuccess
    have hOutput := BinaryPRGWordControllerBooleanResourceSourceWork.materializeWithWork_bound nativeCapacity started.table_correct finished W
      (resource_width_tree 2 s finished hFinal)
    unfold sourceEnvelope
    change started.work + _ + (BinaryPRGWordControllerBooleanResourceSourceWork.materializeWithWork nativeCapacity started.table_correct finished).2 + 2 + 4 ≤
      BinaryPRGWordControllerBooleanResourceSourceWork.inputBound 3 W +
        BinaryPRGWordControllerBooleanResourceInitial.initialBound started.cached.width W 3 +
          bound 2 s started.cached.width seed.width 3 (seed.cap.value - pc.value) +
            BinaryPRGWordControllerBooleanResourceSourceWork.outputBound 3 started.cached.width W + 6
    dsimp only [started] at hRunCap hPreparedWork hOutput ⊢
    omega

def sourceBound (s seedIndexWidth span : ℕ) : ℕ := sourceEnvelope s 4 seedIndexWidth span

theorem sourceEnvelope_mono {s first second seedIndexWidth span : ℕ} (h : first ≤ second) :
    sourceEnvelope s first seedIndexWidth span ≤ sourceEnvelope s second seedIndexWidth span := by
  simp only [sourceEnvelope,bound,pairBound,BinaryPRGWordControllerBooleanResourceInitial.initialBound,
    BinaryPRGWordControllerBooleanResourceInitial.addressBound,BinaryPRGWordControllerBooleanResourcePair.bound,
    BinaryPRGWordControllerBooleanResourceUpdateWork.updateBound,BinaryPRGWordControllerBooleanResourceUpdateWork.fractionalBound,
    BinaryPRGWordControllerBooleanResourceSourceWork.outputBound,BinaryPRGWordControllerBooleanResourceSourceWork.rowsBound]
  gcongr

def sourceRun (seed : BinarySeedLookupTree.Store) (nativeCapacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : BinaryPRGWordControllerThreeResource.Result seed nativeCapacity × ℕ :=
  let drawn := BinaryPRGWordControllerBooleanResourceSourceWork.initialAt seed nativeCapacity resource hC hR pc hp
  ((drawn.1.1.map generalCertified_toThree,drawn.1.2),drawn.2 + 4)

theorem sourceRun_erasure (seed : BinarySeedLookupTree.Store) (nativeCapacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceRun seed nativeCapacity resource hC hR pc hp).1 = BinaryPRGWordControllerThreeResource.run seed nativeCapacity hC
      (BinaryThreeResourcePair.initial nativeCapacity resource hC hR) pc hp := by
  change result_toThree seed nativeCapacity (BinaryPRGWordControllerBooleanResourceSourceWork.initialAt seed nativeCapacity resource hC hR pc hp).1 = _
  rw [BinaryPRGWordControllerBooleanResourceSourceWork.initialAt_erasure,run_toThree,general_toThree_initial]

theorem sourceRun_bound (s : ℕ) (hs : 2 ≤ s) (seed : BinarySeedLookupTree.Store)
    (nativeCapacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (nativeCapacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hCap : ∀ j,RationalHeight (value (nativeCapacity.read j)) s)
    (hResource : ∀ j,RationalHeight (value (resource.read j)) s)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (sourceRun seed nativeCapacity resource hC hR pc hp).2 ≤ sourceBound s seed.width (seed.cap.value - pc.value) :=
  (source_initialAt_bound s hs seed nativeCapacity resource hC hR hCap hResource pc hp).trans
    (sourceEnvelope_mono (BinaryPRGWordControllerBooleanResourceSourceWork.resourceIndex_bound nativeCapacity))

end Blotto.BinaryPRGWordControllerBooleanResourceThreeWork
