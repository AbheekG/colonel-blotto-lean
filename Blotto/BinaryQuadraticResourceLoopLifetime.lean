import Blotto.BinaryQuadraticResourceStateLifetime
import Blotto.BinaryQuadraticResourceSourceLifetime

/-! The complete reached Boolean resource source phase has a retained source
allocation trace: one input tree preparation, initialization, actual quadratic
pair outputs, indexed shared-cap coins, selected path-copy writes/scans, and
final native continuation materialization. Input payload and seed are borrowed;
all newly reserved list/reference regions stay live, without uniqueness or
reclamation. The trace observer itself is ghost evidence, not an execution
cost. Terminal/cache/factory/output continuations and physical pointer-word,
numeric metadata/compiler/allocator interpretation remain separate. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticResourceLoopLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordWalk
open BinaryPRGWordControllerBooleanResourceUpdate BinaryPRGWordControllerBooleanResourcePair
open BinaryPRGWordControllerBooleanResourceLoop BinaryGeneralResourceLattice
open BinaryQuadraticResourceStateLifetime
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def choiceWithTrace (state : Certified capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.state.active = first :: second :: tail) :
    Choice capacity n hCount hC × Trace :=
  let input := source capacity.tree state.state first second tail hC state.canonical state.interior he
  let outputs := BinaryQuadraticResourcePairLifetime.outputsWithTrace input
  (⟨state,first,second,tail,he,outputs.1,by
      rw [BinaryQuadraticResourcePairLifetime.outputsWithTrace_erases]; rfl⟩,
    [.frames 2,.arrayAllocation 40] ++
      under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace capacity.tree first.word).2 ++
      under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace capacity.tree second.word).2 ++
      under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace state.state.resource first.word).2 ++
      under 2 (BinaryQuadraticResourcePairLifetime.lookupWithTrace state.state.resource second.word).2 ++ under 2 outputs.2)

@[simp] theorem choiceWithTrace_erases (state : Certified capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.state.active = first :: second :: tail) :
    (choiceWithTrace (hC := hC) state first second tail he).1 = Choice.prepare hC state first second tail he := by
  simp only [choiceWithTrace,BinaryQuadraticResourcePairLifetime.outputsWithTrace_erases,Choice.prepare,pair]

def preparationBound (w W : ℕ) : ℕ := 20*w + 100 + BinaryQuadraticResourcePairLifetime.outputsBound W
def preparationFrames (w W : ℕ) : ℕ := w + BinaryQuadraticResourcePairLifetime.outputsFrames W + 8

theorem choiceWithTrace_bounds (state : Certified capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.state.active = first :: second :: tail)
    (D : ℕ) (hD : 0 < D)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j,value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D state.reference) :
    cells (choiceWithTrace (hC := hC) state first second tail he).2 ≤ preparationBound capacity.width (3+2*binaryWordWidth D) ∧
      framePeak (choiceWithTrace (hC := hC) state first second tail he).2 ≤ preparationFrames capacity.width (3+2*binaryWordWidth D) := by
  have hHead : state.reference.state.active = first.index n hCount :: second.index n hCount :: tail.map (fun address => address.index n hCount) := by
    rw [state.reference_state]
    simp only [State.reference,he,List.map_cons]
  have ht := pair_trace_wordBounds (capCanonical capacity n hCount hC) state.reference
    (first.index n hCount) (second.index n hCount) (tail.map (fun address => address.index n hCount)) hHead D hD hLattice hUnit hs
  rw [← source_reference capacity.tree state.state first second tail hC state.canonical state.interior he
    n hCount _ state.reference state.reference_state] at ht
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
  unfold choiceWithTrace preparationBound preparationFrames
  simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by omega,by omega⟩

def prepareWithTrace (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) : Preparation capacity n hCount hC × Trace :=
  match he : state.state.active with
  | first :: second :: tail =>
      let choice := choiceWithTrace (hC := hC) state first second tail he
      (.ask choice.1,[.frames 2,.arrayAllocation 8] ++ under 2 choice.2)
  | _ => (.done state,[.frames 1,.arrayAllocation 8])

@[simp] theorem prepareWithTrace_erases (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) : (prepareWithTrace capacity n hCount hC state).1 = prepare capacity n hCount hC state := by
  cases state with
  | mk data certified => cases data with
    | mk tree active => cases active with
      | nil => rfl
      | cons first rest => cases rest with
        | nil => rfl
        | cons second tail => simp only [prepareWithTrace,BinaryPRGWordControllerBooleanResourceLoop.prepare,choiceWithTrace_erases]

theorem prepareWithTrace_bounds (D : ℕ) (hD : 0 < D)
    (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j,value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D state.reference) :
    cells (prepareWithTrace capacity n hCount hC state).2 ≤ preparationBound capacity.width (3+2*binaryWordWidth D) + 8 ∧
      framePeak (prepareWithTrace capacity n hCount hC state).2 ≤ preparationFrames capacity.width (3+2*binaryWordWidth D) + 2 := by
  unfold prepareWithTrace
  split
  · rename_i first second tail he
    have hp := choiceWithTrace_bounds (hC := hC) state first second tail he D hD hLattice hUnit hs
    have hf := framePeak_under 2 (choiceWithTrace (hC := hC) state first second tail he).2
    simp only [cells] at hp
    simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
    exact ⟨by omega,by omega⟩
  · simp [cells,listCells,arraySlots,framePeak]

def selectWithTrace (choice : Choice capacity n hCount hC) (branch : Bool) : Certified capacity n hCount × Trace :=
  let selected := BinaryQuadraticResourceStateLifetime.updateWithTrace capacity.tree choice.state.state
    choice.first choice.second choice.tail (choice.endpoint branch)
  (⟨selected.1,by rw [BinaryQuadraticResourceStateLifetime.updateWithTrace_erases]; exact (choice.select branch).certified⟩,
    [.frames 2,.arrayAllocation 16] ++ under 2 selected.2)

@[simp] theorem selectWithTrace_erases (choice : Choice capacity n hCount hC) (branch : Bool) :
    (selectWithTrace choice branch).1 = choice.select branch := by
  apply BinaryPRGWordControllerBooleanResourceLoopWork.certified_ext
  exact BinaryQuadraticResourceStateLifetime.updateWithTrace_erases _ _ _ _ _ _

theorem selectWithTrace_bounds (D : ℕ) (hD : 0 < D) (choice : Choice capacity n hCount hC)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D choice.state.reference) (branch : Bool) :
    cells (selectWithTrace choice branch).2 ≤ updateBound capacity.width (3+2*binaryWordWidth D) + 16 ∧
      framePeak (selectWithTrace choice branch).2 ≤ updateFrames capacity.width (3+2*binaryWordWidth D) + 2 := by
  have hu : ∀ j,value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1 := fun j => (hBox j).2
  have hChosen := BinaryGeneralResourceExecution.selected_endpoint_width choice.original.original D hD hLattice hu hs branch
  rw [← choice.original.endpoint_original,← choice.endpoint_original] at hChosen
  have hTotal := BinaryGeneralResourceExecution.selected_total_width choice.original.original D hD hLattice hu hs
  have hOther := BinaryGeneralResourceExecution.selected_other_width choice.original.original D hD hLattice hu hs branch
  rw [← choice.original.endpoint_original,← choice.endpoint_original] at hOther
  simp only [BinaryPRGWordControllerGeneralChoice.Choice.original,Choice.original,
    Certified.reference_state,State.reference,table_read] at hTotal hOther
  have ha := apply_native .add _ _ (choice.state.canonical choice.first).1 (choice.state.canonical choice.second).1
  have ht : BinaryRationalOpcode.Valid (BinaryQuadraticData.apply .add
      (lookup choice.state.state.resource choice.first.word) (lookup choice.state.state.resource choice.second.word)) := by
    rw [ha]
    exact BinaryRationalOpcode.apply_valid .add _ _ (choice.state.canonical choice.first).1 (choice.state.canonical choice.second).1
  have hb := apply_native .sub _ _ ht (choice.endpoint_canonical branch).1
  rw [ha] at hb
  have hp := BinaryQuadraticResourceStateLifetime.updateWithTrace_bounds capacity.tree choice.state.state
    choice.first choice.second choice.tail (choice.endpoint branch) (3+2*binaryWordWidth D) (by omega)
    (BinaryPRGWordControllerBooleanResourceLoopWork.state_width D hD choice.state hu hs)
    (BinaryPRGWordControllerBooleanResourceLoopWork.capacity_width D hD hC hLattice hBox)
    (by omega) (by rw [ha]; omega) (by rw [ha,hb]; omega)
  have hf := framePeak_under 2 (BinaryQuadraticResourceStateLifetime.updateWithTrace capacity.tree choice.state.state
    choice.first choice.second choice.tail (choice.endpoint branch)).2
  simp only [cells] at hp
  unfold selectWithTrace
  simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
  exact ⟨by omega,by omega⟩

def runWithTrace (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Result seed capacity n hCount × Trace :=
  let prepared := prepareWithTrace capacity n hCount hC state
  match hs : prepared.1 with
  | .done result => ((some result,pc),[.frames 2,.arrayAllocation 16] ++ under 2 prepared.2)
  | .ask choice =>
      let coin := BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp
      match coin.1.1 with
      | none => ((none,coin.1.2),[.frames 2,.arrayAllocation 24] ++ under 2 prepared.2 ++ under 2 coin.2)
      | some branch =>
          let selected := selectWithTrace choice branch
          let later := runWithTrace seed capacity n hCount hC selected.1 coin.1.2
            (BinaryWordCoinLifetime.sampleWithTrace_position seed choice.probability pc hp).2
          (later.1,[.frames 2,.arrayAllocation 32] ++ under 2 prepared.2 ++ under 2 coin.2 ++ under 2 selected.2 ++ under 1 later.2)
termination_by state.state.active.length
decreasing_by
  rw [selectWithTrace_erases]
  have hw := prepared_state state choice ((prepareWithTrace_erases capacity n hCount hC state).symm.trans hs)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

@[simp] theorem runWithTrace_erases (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (runWithTrace seed capacity n hCount hC state pc hp).1 = run seed capacity n hCount hC state pc hp := by
  conv_lhs => unfold runWithTrace
  conv_rhs => unfold run
  rw [← prepareWithTrace_erases capacity n hCount hC state]
  dsimp only
  cases hs : (prepareWithTrace capacity n hCount hC state).1 with
  | done result => rfl
  | ask choice =>
      dsimp only
      simp only [BinaryWordCoinLifetime.sampleWithTrace_erases]
      cases hc : (BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp).1 with
      | none => rfl
      | some branch =>
          dsimp only
          rw [selectWithTrace_erases]
          exact runWithTrace_erases seed capacity n hCount hC (choice.select branch)
            (BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp).2
            (BinaryPRGWordControllerDataCoin.sample_position seed choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := prepared_state state choice ((prepareWithTrace_erases capacity n hCount hC state).symm.trans hs)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

def loopStep (D w seedWidth N : ℕ) : ℕ :=
  preparationBound w (3+2*binaryWordWidth D) + updateBound w (3+2*binaryWordWidth D) +
    BinaryWordCoinLifetime.sampleBound (3+2*binaryWordWidth D) seedWidth N + 80
def loopFrames (D w seedWidth N : ℕ) : ℕ :=
  preparationFrames w (3+2*binaryWordWidth D) + updateFrames w (3+2*binaryWordWidth D) + N +
    2*(3+2*binaryWordWidth D) + 2*seedWidth + 60

theorem runWithTrace_bounds (D : ℕ) (hD : 0 < D) (seed : BinarySeedLookupTree.Store)
    (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧ value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D state.reference)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    cells (runWithTrace seed capacity n hCount hC state pc hp).2 ≤
      (state.state.active.length+1)*loopStep D capacity.width seed.width seed.cap.value ∧
    framePeak (runWithTrace seed capacity n hCount hC state pc hp).2 ≤
      (state.state.active.length+1)*loopFrames D capacity.width seed.width seed.cap.value := by
  have hPre := prepareWithTrace_bounds D hD capacity n hCount hC state hLattice (fun j => (hBox j).2) hs
  have hFrameBase : loopFrames D capacity.width seed.width seed.cap.value ≤
      (state.state.active.length+1)*loopFrames D capacity.width seed.width seed.cap.value :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold runWithTrace
  dsimp only
  cases hPrepared : (prepareWithTrace capacity n hCount hC state).1 with
  | done result =>
      have hf := framePeak_under 2 (prepareWithTrace capacity n hCount hC state).2
      simp only [cells] at hPre
      simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
      unfold loopStep
      unfold loopFrames at hFrameBase ⊢
      exact ⟨by nlinarith only [hPre.1],by omega⟩
  | ask choice =>
      dsimp only
      have hw := prepared_state state choice ((prepareWithTrace_erases capacity n hCount hC state).symm.trans hPrepared)
      have hChoice : StateInvariant (table capacity.cap capacity.tree n hCount) D choice.state.reference := hw.symm ▸ hs
      have hWidth := prepared_coin_buffer_width choice.original.original D hD hLattice (fun j => (hBox j).2) hChoice
      rw [← choice.original.probability_original,← choice.probability_original] at hWidth
      change width choice.probability ≤ 1+2*binaryWordWidth D at hWidth
      have hCoin := BinaryWordCoinLifetime.sampleWithTrace_bounds seed choice.probability pc hp (3+2*binaryWordWidth D) (by omega)
      have hCoinCap : cells (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).2 ≤
          BinaryWordCoinLifetime.sampleBound (3+2*binaryWordWidth D) seed.width seed.cap.value := by
        apply hCoin.1.trans
        unfold BinaryWordCoinLifetime.sampleBound
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)) _
      have pf := framePeak_under 2 (prepareWithTrace capacity n hCount hC state).2
      have cf := framePeak_under 2 (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).2
      cases hcoin : (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).1.1 with
      | none =>
          simp only [cells] at hPre hCoinCap
          simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
          unfold loopStep
          unfold loopFrames at hFrameBase ⊢
          exact ⟨by nlinarith only [hPre.1,hCoinCap],by omega⟩
      | some branch =>
          dsimp only
          have hSelect := selectWithTrace_bounds D hD choice hLattice hBox hChoice branch
          have hNext := choice_select_invariant choice.original.original D hLattice hChoice branch
          rw [← choice.original.select_original,← choice.select_original,← selectWithTrace_erases] at hNext
          have ih := runWithTrace_bounds D hD seed capacity n hCount hC (selectWithTrace choice branch).1 hLattice hBox hNext
            (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).1.2
            (BinaryWordCoinLifetime.sampleWithTrace_position seed choice.probability pc hp).2
          have hLength := choice.select_progress branch
          rw [hw,← selectWithTrace_erases] at hLength
          have sf := framePeak_under 2 (selectWithTrace choice branch).2
          have lf := framePeak_under 1 (runWithTrace seed capacity n hCount hC (selectWithTrace choice branch).1
            (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).1.2
            (BinaryWordCoinLifetime.sampleWithTrace_position seed choice.probability pc hp).2).2
          simp only [cells] at hPre hCoinCap hSelect ih
          simp only [cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,framePeak_append,framePeak]
          have hStepPos : 1 ≤ loopStep D capacity.width seed.width seed.cap.value := by unfold loopStep; omega
          have hFramePos : 4 ≤ loopFrames D capacity.width seed.width seed.cap.value := by unfold loopFrames; omega
          have hRanks : (selectWithTrace choice branch).1.state.active.length+1 ≤ state.state.active.length := by omega
          have hRanksFrames := Nat.mul_le_mul_right (loopFrames D capacity.width seed.width seed.cap.value) hRanks
          have hLaterFrames : framePeak (under 1 (runWithTrace seed capacity n hCount hC (selectWithTrace choice branch).1
              (BinaryWordCoinLifetime.sampleWithTrace seed choice.probability pc hp).1.2
              (BinaryWordCoinLifetime.sampleWithTrace_position seed choice.probability pc hp).2).2) ≤
              (state.state.active.length+1)*loopFrames D capacity.width seed.width seed.cap.value := by
            nlinarith only [lf,ih.2,hRanksFrames,hFramePos]
          have hIHCells := ih.1
          have hIHFrames := ih.2
          unfold loopStep at hIHCells ⊢
          unfold loopFrames at hIHFrames hFrameBase hLaterFrames ⊢
          exact ⟨by nlinarith only [hPre.1,hCoinCap,hSelect.1,hIHCells,hLength],
            by omega⟩
termination_by state.state.active.length
decreasing_by
  rw [selectWithTrace_erases]
  have hw := prepared_state state choice ((prepareWithTrace_erases capacity n hCount hC state).symm.trans hPrepared)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

def sourceRunWithTrace (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    BinaryPRGWordControllerResource.Result seed capacity × Trace :=
  let started := BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace capacity resource hC hR
  let drawn := runWithTrace seed (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity) n
    (BinaryPRGWordControllerBooleanResourceSource.source_count capacity)
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC) started.1
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  match drawn.1.1 with
  | none => ((none,drawn.1.2),[.frames (seed.width+2),.listAllocation seed.width,.arrayAllocation 24] ++
      under 2 started.2 ++ under 2 drawn.2)
  | some state =>
      let output := BinaryQuadraticResourceSourceLifetime.materializeWithTrace capacity
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity) state
      ((some output.1,drawn.1.2),[.frames (seed.width+2),.listAllocation seed.width,.arrayAllocation 24] ++
        under 2 started.2 ++ under 2 drawn.2 ++ under 2 output.2)

@[simp] theorem sourceRunWithTrace_erases (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (sourceRunWithTrace seed capacity resource hC hR).1 =
      BinaryPRGWordControllerBooleanResourceSource.initialRun seed capacity resource hC hR := by
  unfold sourceRunWithTrace BinaryPRGWordControllerBooleanResourceSource.initialRun BinaryPRGWordControllerBooleanResourceSource.result
  dsimp only
  rw [BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace_erases,runWithTrace_erases]
  cases hs : (run seed (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity) n
      (BinaryPRGWordControllerBooleanResourceSource.source_count capacity)
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      (BinaryPRGWordControllerBooleanResourceSource.initial capacity resource hC hR)
      (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)).1 with
  | none => rfl
  | some state =>
      simp only [Option.map_some,BinaryQuadraticResourceSourceLifetime.materializeWithTrace_erases]
      rfl

theorem sourceRunWithTrace_work_erases (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (sourceRunWithTrace seed capacity resource hC hR).1 =
      (BinaryPRGWordControllerBooleanResourceSourceWork.initialRun seed capacity resource hC hR).1 := by
  rw [sourceRunWithTrace_erases,BinaryPRGWordControllerBooleanResourceSource.initialRun_original,
    BinaryPRGWordControllerBooleanResourceSourceWork.initialRun_erasure]

def sourceBound (n D w seedWidth N : ℕ) : ℕ :=
  BinaryQuadraticResourceSourceLifetime.startBound n w (3+2*binaryWordWidth D) +
    (n+1)*loopStep D w seedWidth N + BinaryQuadraticResourceSourceLifetime.outputBound n w + seedWidth + 24
def sourceFrames (n D w seedWidth N : ℕ) : ℕ :=
  BinaryQuadraticResourceSourceLifetime.startFrames n w (3+2*binaryWordWidth D) +
    (n+1)*loopFrames D w seedWidth N + BinaryQuadraticResourceSourceLifetime.outputFrames n w + seedWidth + 10

theorem sourceRunWithTrace_bounds (D : ℕ) (hD : 0 < D) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResource : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) :
    cells (sourceRunWithTrace seed capacity resource hC hR).2 ≤
      sourceBound n D (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value ∧
    framePeak (sourceRunWithTrace seed capacity resource hC hR).2 ≤
      sourceFrames n D (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value := by
  let cached := BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity
  let hCount := BinaryPRGWordControllerBooleanResourceSource.source_count capacity
  let hc := BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC
  let started := BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace capacity resource hC hR
  have hNative := BinaryGeneralResourceLattice.initial_invariant capacity resource hC hR D hResource hResourceBox
  have hCapWord : ∀ j,width (capacity.read j) ≤ 3+2*binaryWordWidth D := by
    intro j
    have h := capacity_wordWidth capacity hC D hD hLattice hBox j
    omega
  have hResWord : ∀ j,width (resource.read j) ≤ 3+2*binaryWordWidth D := by
    intro j
    have h := state_wordWidth (BinaryResourcePair.initial capacity resource hC hR) D hD (fun j => (hBox j).2) hNative j
    change width (resource.read j) ≤ _ at h
    omega
  have hCapTree : ∀ address : Address cached.width cached.cap,width (lookup cached.tree address.word) ≤ 3+2*binaryWordWidth D := by
    intro address
    have hRead := table_read cached.tree address n hCount
    have hTable := congrArg (fun t : FixedArrayTable n SignedWord => t.read (address.index n hCount))
      (BinaryPRGWordControllerBooleanResourceSource.capacityTable capacity)
    rw [← hRead,hTable]
    exact hCapWord _
  have hResTree : ∀ address : Address cached.width cached.cap,
      width (lookup (BinaryPRGWordControllerBooleanResourceSource.resourceStore capacity resource).tree address.word) ≤ 3+2*binaryWordWidth D := by
    intro address
    have hRead := table_read (BinaryPRGWordControllerBooleanResourceSource.resourceStore capacity resource).tree address n hCount
    have hTable := congrArg (fun t : FixedArrayTable n SignedWord => t.read (address.index n hCount))
      (BinaryPRGWordControllerBooleanResourceSource.resourceTable capacity resource)
    exact (hTable.symm.trans hRead) ▸ hResWord (address.index n hCount)
  have hStart := BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace_bounds capacity resource hC hR
    (3+2*binaryWordWidth D) (by omega) hCapTree hResTree
  have hs : StateInvariant (table cached.cap cached.tree n hCount) D started.1.reference := by
    rw [BinaryQuadraticResourceSourceLifetime.sourceInitialWithTrace_erases]
    exact BinaryPRGWordControllerBooleanResourceSourceWork.initial_invariant capacity resource hC hR D hResource hResourceBox
  have hLatticeTree : ∀ j,OnRationalLattice D (value ((table cached.cap cached.tree n hCount).read j)) := by
    intro j
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hLattice j
  have hBoxTree : ∀ j,0 ≤ value ((table cached.cap cached.tree n hCount).read j) ∧ value ((table cached.cap cached.tree n hCount).read j) ≤ 1 := by
    intro j
    rw [BinaryPRGWordControllerBooleanResourceSource.capacityTable]
    exact hBox j
  let drawn := runWithTrace seed cached n hCount hc started.1 (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  have hRun := runWithTrace_bounds D hD seed cached n hCount hc started.1 hLatticeTree hBoxTree hs
    (BinaryWordIndexCoinController.zeroIndex seed) (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  have hActive := BinaryGeneralResourceRun.active_length_le started.1.reference
  rw [started.1.reference_state] at hActive
  simp only [State.reference,List.length_map] at hActive
  have hRunCells : cells drawn.2 ≤ (n+1)*loopStep D cached.width seed.width seed.cap.value :=
    hRun.1.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hActive 1))
  have hRunFrames : framePeak drawn.2 ≤ (n+1)*loopFrames D cached.width seed.width seed.cap.value :=
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

open scoped BigOperators
def inputCells (capacity resource : FixedArrayTable n SignedWord) : ℕ := 16+2*n+
  (∑ j,BinaryRationalOpcodeAllocation.payload (capacity.read j)) +
  (∑ j,BinaryRationalOpcodeAllocation.payload (resource.read j))

theorem source_all_prefix_heap (D : ℕ) (hD : 0 < D) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResource : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j))
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (inputCells capacity resource + BinaryWordStoreLifetime.storeCells seed + originalSeedCells + borrowedOtherCells)
      (sourceRunWithTrace seed capacity resource hC hR).2 steps ≤
      inputCells capacity resource + BinaryWordStoreLifetime.storeCells seed + originalSeedCells + borrowedOtherCells +
        sourceBound n D (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _
    (sourceRunWithTrace_bounds D hD seed capacity resource hC hR hLattice hResource hBox hResourceBox).1

theorem source_all_prefix_frames (D : ℕ) (hD : 0 < D) (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hResource : ∀ j,OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j,0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceBox : ∀ j,0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) (steps : ℕ) :
    framePeak ((sourceRunWithTrace seed capacity resource hC hR).2.take steps) ≤
      sourceFrames n D (BinaryPRGWordControllerBooleanResourceSource.capacityStore capacity).width seed.width seed.cap.value :=
  (framePeak_take_le _ _).trans (sourceRunWithTrace_bounds D hD seed capacity resource hC hR hLattice hResource hBox hResourceBox).2

def requestWithTrace (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    BinaryPRGWordControllerResource.Result seed (BinaryPRGResourceWork.resourceInput request rich).length × Trace :=
  sourceRunWithTrace seed (BinaryPRGResourceWork.resourceInput request rich).length
    (BinaryPRGResourceWork.resourceInput request rich).resource
    (BinaryPRGResourceWork.resource_canonical request rich).2.1 (BinaryPRGResourceWork.resource_canonical request rich).2.2

theorem requestWithTrace_erases (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (requestWithTrace seed request rich).1 = (BinaryPRGWordControllerBooleanResourceSourceWork.requestRun seed request rich).1 :=
  sourceRunWithTrace_work_erases _ _ _ _ _

def requestBound (n S seedWidth N : ℕ) : ℕ :=
  let w := n+1
  let W := 5+2*S
  BinaryQuadraticResourceSourceLifetime.startBound n w W + (n+1)*
    (preparationBound w W + updateBound w W + BinaryWordCoinLifetime.sampleBound W seedWidth N + 80) +
      BinaryQuadraticResourceSourceLifetime.outputBound n w + seedWidth + 24
def requestFrames (n S seedWidth N : ℕ) : ℕ :=
  let w := n+1
  let W := 5+2*S
  BinaryQuadraticResourceSourceLifetime.startFrames n w W + (n+1)*
    (preparationFrames w W + updateFrames w W + N + 2*W + 2*seedWidth + 60) +
      BinaryQuadraticResourceSourceLifetime.outputFrames n w + seedWidth + 10

theorem sourceBound_le_requestBound (n D w S seedWidth N : ℕ) (hWidth : w ≤ n+1)
    (hD : binaryWordWidth D ≤ S+1) : sourceBound n D w seedWidth N ≤ requestBound n S seedWidth N := by
  have hW : 3+2*binaryWordWidth D ≤ 5+2*S := by omega
  unfold sourceBound requestBound loopStep BinaryQuadraticResourceSourceLifetime.startBound
    BinaryQuadraticResourceSourceLifetime.outputBound BinaryQuadraticResourceStateLifetime.initialBound
    addressStep fractionalBound compareBound preparationBound updateBound BinaryQuadraticResourcePairLifetime.outputsBound
    BinaryQuadraticResourcePairLifetime.pairBound BinaryQuadraticResourcePairLifetime.instructionBound
    BinaryQuadraticLifetime.opcodeBound BinaryWordCoinLifetime.sampleBound BinaryWordCoinLifetime.localBound
  dsimp only
  simp only [fractionalBound,compareBound]
  gcongr

theorem sourceFrames_le_requestFrames (n D w S seedWidth N : ℕ) (hWidth : w ≤ n+1)
    (hD : binaryWordWidth D ≤ S+1) : sourceFrames n D w seedWidth N ≤ requestFrames n S seedWidth N := by
  have hW : 3+2*binaryWordWidth D ≤ 5+2*S := by omega
  unfold sourceFrames requestFrames loopFrames BinaryQuadraticResourceSourceLifetime.startFrames
    BinaryQuadraticResourceSourceLifetime.outputFrames BinaryQuadraticResourceStateLifetime.initialFrames
    fractionalFrames compareFrames preparationFrames updateFrames BinaryQuadraticResourcePairLifetime.outputsFrames
    BinaryQuadraticResourcePairLifetime.pairFrames BinaryQuadraticResourcePairLifetime.instructionFrames
    BinaryQuadraticLifetime.opcodeFrames
  dsimp only
  simp only [fractionalFrames,compareFrames]
  gcongr

theorem requestWithTrace_bounds (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    cells (requestWithTrace seed request rich).2 ≤ requestBound n request.source.originalInputWordWidth seed.width seed.cap.value ∧
      framePeak (requestWithTrace seed request rich).2 ≤ requestFrames n request.source.originalInputWordWidth seed.width seed.cap.value := by
  obtain ⟨hL,hR,hBox,hResourceBox⟩ := BinaryPRGResourceWork.resource_lattice_boxes request rich
  have h := sourceRunWithTrace_bounds request.source.normalizedInput.latticeDenominator
    request.source.normalizedInput.latticeDenominator_pos seed _ _
    (BinaryPRGResourceWork.resource_canonical request rich).2.1 (BinaryPRGResourceWork.resource_canonical request rich).2.2
    hL hR hBox hResourceBox
  have hWidth := BinaryPRGWordControllerBooleanResourceSourceWork.resourceIndex_bound (BinaryPRGResourceWork.resourceInput request rich).length
  have hD := request.source.normalized_lattice_wordWidth_original
  exact ⟨h.1.trans (sourceBound_le_requestBound _ _ _ _ _ _ hWidth (by omega)),
    h.2.trans (sourceFrames_le_requestFrames _ _ _ _ _ _ hWidth (by omega))⟩

theorem request_all_prefix_heap (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (originalSeedCells borrowedOtherCells steps : ℕ) :
    retainedHeap (inputCells (BinaryPRGResourceWork.resourceInput request rich).length (BinaryPRGResourceWork.resourceInput request rich).resource +
      BinaryWordStoreLifetime.storeCells seed + originalSeedCells + borrowedOtherCells) (requestWithTrace seed request rich).2 steps ≤
      inputCells (BinaryPRGResourceWork.resourceInput request rich).length (BinaryPRGResourceWork.resourceInput request rich).resource +
        BinaryWordStoreLifetime.storeCells seed + originalSeedCells + borrowedOtherCells +
          requestBound n request.source.originalInputWordWidth seed.width seed.cap.value :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (requestWithTrace_bounds seed request rich).1

theorem request_all_prefix_frames (seed : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) (steps : ℕ) :
    framePeak ((requestWithTrace seed request rich).2.take steps) ≤ requestFrames n request.source.originalInputWordWidth seed.width seed.cap.value :=
  (framePeak_take_le _ _).trans (requestWithTrace_bounds seed request rich).2

end Blotto.BinaryQuadraticResourceLoopLifetime
