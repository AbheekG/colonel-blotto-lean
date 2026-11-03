import Blotto.BinaryPRGWordControllerBooleanResourceLoop
import Blotto.BinaryGeneralResourceExecution

/-! The Boolean outer resource runner records its own reached pair,
selected tree update and coin work. Exact erasure and fixed-lattice derived
bounds are separate: native result equality alone transfers no price. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourceLoopWork
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourceUpdateWork BinaryPRGWordControllerBooleanResourcePair
open BinaryPRGWordControllerBooleanResourceLoop

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

theorem certified_ext (first second : Certified capacity n hCount) (h : first.state = second.state) : first = second := by
  cases first
  cases second
  cases h
  rfl

def prepareChoiceWithWork (state : Certified capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.state.active = first :: second :: tail) :
    Choice capacity n hCount hC × ℕ :=
  let prepared := pairWithWork capacity.tree state.state first second tail hC state.canonical state.interior he
  (⟨state,first,second,tail,he,prepared.1,pairWithWork_erasure _ _ _ _ _ _ _ _ _⟩,prepared.2)

theorem prepareChoiceWithWork_erasure (state : Certified capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.state.active = first :: second :: tail) :
    (prepareChoiceWithWork (hC := hC) state first second tail he).1 = Choice.prepare hC state first second tail he := by
  unfold prepareChoiceWithWork Choice.prepare
  simp only [pairWithWork_erasure]

def prepareWithWork (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) : Preparation capacity n hCount hC × ℕ :=
  match he : state.state.active with
  | first :: second :: tail =>
      let choice := prepareChoiceWithWork (hC := hC) state first second tail he
      (.ask choice.1,choice.2 + 1)
  | _ => (.done state,1)

theorem prepareWithWork_erasure (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) : (prepareWithWork capacity n hCount hC state).1 = prepare capacity n hCount hC state := by
  cases state with
  | mk data certified =>
    cases data with
    | mk tree active =>
      cases active with
      | nil => rfl
      | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second tail =>
          dsimp only [prepareWithWork,BinaryPRGWordControllerBooleanResourceLoop.prepare]
          rw [prepareChoiceWithWork_erasure]

def selectWithWork (choice : Choice capacity n hCount hC) (branch : Bool) : Certified capacity n hCount × ℕ :=
  let selected := updateWithWork capacity.tree choice.state.state choice.first choice.second choice.tail (choice.endpoint branch)
  (⟨selected.1,by rw [updateWithWork_erasure]; exact (choice.select branch).certified⟩,selected.2)

theorem selectWithWork_erasure (choice : Choice capacity n hCount hC) (branch : Bool) :
    (selectWithWork choice branch).1 = choice.select branch := by
  apply certified_ext
  exact updateWithWork_erasure _ _ _ _ _ _

def run (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Result seed capacity n hCount × ℕ :=
  let prepared := prepareWithWork capacity n hCount hC state
  match hs : prepared.1 with
  | .done result => ((some result,pc),prepared.2 + 2)
  | .ask choice =>
      let coin := BinaryWordIndexCoinController.sample seed choice.probability pc hp
      match coin.1.1 with
      | none => ((none,coin.1.2),prepared.2 + coin.2 + 2)
      | some branch =>
          let selected := selectWithWork choice branch
          let later := run seed capacity n hCount hC selected.1 coin.1.2
            (BinaryWordIndexCoinController.sample_position_bounds seed choice.probability pc hp).2
          (later.1,prepared.2 + coin.2 + selected.2 + later.2 + 2)
termination_by state.state.active.length
decreasing_by
  rw [selectWithWork_erasure]
  have hw := prepared_state state choice ((prepareWithWork_erasure capacity n hCount hC state).symm.trans hs)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_erasure (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed capacity n hCount hC state pc hp).1 =
      BinaryPRGWordControllerBooleanResourceLoop.run seed capacity n hCount hC state pc hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinaryPRGWordControllerBooleanResourceLoop.run
  rw [← prepareWithWork_erasure capacity n hCount hC state]
  dsimp only
  cases hs : (prepareWithWork capacity n hCount hC state).1 with
  | done result => rfl
  | ask choice =>
      dsimp only
      simp only [BinaryPRGWordControllerDataCoin.sample_erasure]
      cases hc : (BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp).1 with
      | none => rfl
      | some branch =>
          dsimp only
          rw [selectWithWork_erasure]
          exact run_erasure seed capacity n hCount hC (choice.select branch)
            (BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp).2
            (BinaryPRGWordControllerDataCoin.sample_position seed choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := prepared_state state choice ((prepareWithWork_erasure capacity n hCount hC state).symm.trans hs)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

open BinaryGeneralResourceLattice
set_option maxHeartbeats 1000000

def widthBound (D : ℕ) : ℕ := 3 + 2 * binaryWordWidth D

theorem capacity_width (D : ℕ) (hD : 0 < D)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (address : Address capacity.width capacity.cap) : width (lookup capacity.tree address.word) ≤ widthBound D := by
  have h := capacity_wordWidth (table capacity.cap capacity.tree n hCount) (capCanonical capacity n hCount hC)
    D hD hLattice hBox (address.index n hCount)
  rw [table_read] at h
  unfold widthBound
  omega

theorem state_width (D : ℕ) (hD : 0 < D) (state : Certified capacity n hCount)
    (hUnit : ∀ j,value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D state.reference)
    (address : Address capacity.width capacity.cap) : width (lookup state.state.resource address.word) ≤ widthBound D := by
  have h := state_wordWidth state.reference D hD hUnit hs (address.index n hCount)
  rw [state.reference_state] at h
  simp only [State.reference,table_read] at h
  unfold widthBound
  omega

theorem prepareWithWork_bound (D : ℕ) (hD : 0 < D)
    (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hUnit : ∀ j,value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D state.reference) :
    (prepareWithWork capacity n hCount hC state).2 ≤ BinaryPRGWordControllerBooleanResourcePair.bound capacity.width (widthBound D) + 1 := by
  unfold prepareWithWork
  split
  · rename_i first second tail he
    have hNative : state.reference.state.active = first.index n hCount :: second.index n hCount :: tail.map (fun address => address.index n hCount) := by
      rw [state.reference_state]
      simp only [State.reference,he,List.map_cons]
    have hTrace := pair_trace_wordBounds (capCanonical capacity n hCount hC) state.reference
      (first.index n hCount) (second.index n hCount) (tail.map (fun address => address.index n hCount)) hNative
      D hD hLattice hUnit hs
    rw [← source_reference capacity.tree state.state first second tail hC state.canonical state.interior he
      n hCount (capCanonical capacity n hCount hC) state.reference state.reference_state] at hTrace
    have hPair := pairWithWork_bound capacity.tree state.state first second tail hC state.canonical state.interior he (widthBound D) hTrace
    exact Nat.add_le_add_right hPair 1
  · omega

theorem selectWithWork_bound (D : ℕ) (hD : 0 < D) (choice : Choice capacity n hCount hC)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D choice.state.reference) (branch : Bool) :
    (selectWithWork choice branch).2 ≤ updateBound capacity.width (widthBound D) n := by
  have hu : ∀ j,value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1 := fun j => (hBox j).2
  have hChosen := BinaryGeneralResourceExecution.selected_endpoint_width choice.original.original D hD hLattice hu hs branch
  rw [← choice.original.endpoint_original,← choice.endpoint_original] at hChosen
  have hTotal := BinaryGeneralResourceExecution.selected_total_width choice.original.original D hD hLattice hu hs
  have hOther := BinaryGeneralResourceExecution.selected_other_width choice.original.original D hD hLattice hu hs branch
  rw [← choice.original.endpoint_original,← choice.endpoint_original] at hOther
  simp only [BinaryPRGWordControllerGeneralChoice.Choice.original,Choice.original,
    Certified.reference_state,State.reference,table_read] at hTotal hOther
  have hFirst := (choice.state.canonical choice.first).1
  have hSecond := (choice.state.canonical choice.second).1
  have ha := apply_native .add _ _ hFirst hSecond
  have ht : BinaryRationalOpcode.Valid (BinaryQuadraticData.apply .add
      (lookup choice.state.state.resource choice.first.word) (lookup choice.state.state.resource choice.second.word)) := by
    rw [ha]
    exact BinaryRationalOpcode.apply_valid .add _ _ hFirst hSecond
  have hb := apply_native .sub _ _ ht (choice.endpoint_canonical branch).1
  rw [ha] at hb
  have hUpdate := updateWithWork_bound capacity.tree choice.state.state choice.first choice.second choice.tail
    (choice.endpoint branch) (widthBound D) (by unfold widthBound; omega)
    (state_width D hD choice.state hu hs) (capacity_width D hD hC hLattice hBox)
    (by unfold widthBound; omega)
    (by rw [ha]; unfold widthBound; omega)
    (by rw [ha,hb]; unfold widthBound; omega)
  have hLength : choice.tail.length ≤ n := by
    have hn := BinaryGeneralResourceRun.active_length_le choice.state.reference
    rw [choice.state.reference_state] at hn
    simp only [State.reference,List.length_map,choice.head_pair,List.length_cons] at hn
    omega
  exact hUpdate.trans (by unfold updateBound; nlinarith)

def pairBound (n D resourceIndexWidth seedIndexWidth : ℕ) : ℕ :=
  BinaryPRGWordControllerBooleanResourcePair.bound resourceIndexWidth (widthBound D) + 1 +
    updateBound resourceIndexWidth (widthBound D) n + 12 * (2 + 2 * binaryWordWidth D) +
      BinaryPRGWordControllerResource.bodyBound D seedIndexWidth + 2

def bound (n D resourceIndexWidth seedIndexWidth active span : ℕ) : ℕ :=
  (active + 1) * pairBound n D resourceIndexWidth seedIndexWidth +
    span * BinaryPRGWordControllerResource.bodyBound D seedIndexWidth

theorem run_bound (D : ℕ) (hD : 0 < D) (seed : BinarySeedLookupTree.Store)
    (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hBox : ∀ j,0 ≤ value ((table capacity.cap capacity.tree n hCount).read j) ∧
      value ((table capacity.cap capacity.tree n hCount).read j) ≤ 1)
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D state.reference)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed capacity n hCount hC state pc hp).2 ≤ bound n D capacity.width seed.width state.state.active.length
      ((run seed capacity n hCount hC state pc hp).1.2.value - pc.value) := by
  have hPreparation := prepareWithWork_bound D hD capacity n hCount hC state hLattice (fun j => (hBox j).2) hs
  conv_lhs => unfold run
  conv_rhs => arg 6; arg 1; arg 1; unfold run
  dsimp only
  cases hPrepared : (prepareWithWork capacity n hCount hC state).1 with
  | done result =>
      simp only [Nat.sub_self]
      unfold bound pairBound
      nlinarith
  | ask choice =>
      dsimp only
      have hw := prepared_state state choice ((prepareWithWork_erasure capacity n hCount hC state).symm.trans hPrepared)
      have hChoice : StateInvariant (table capacity.cap capacity.tree n hCount) D choice.state.reference := hw.symm ▸ hs
      have hCoin := BinaryPRGWordControllerResource.coin_bound D hD seed choice.original hLattice
        (fun j => (hBox j).2) hChoice pc hp
      simp only [← choice.probability_original] at hCoin
      have hPosition := BinaryWordIndexCoinController.sample_position_bounds seed choice.probability pc hp
      cases hcoin : (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.1 with
      | none => unfold bound pairBound; nlinarith
      | some branch =>
          dsimp only
          have hSelect := selectWithWork_bound D hD choice hLattice hBox hChoice branch
          have hNext := choice_select_invariant choice.original.original D hLattice hChoice branch
          rw [← choice.original.select_original,← choice.select_original,← selectWithWork_erasure] at hNext
          have ih := run_bound D hD seed capacity n hCount hC (selectWithWork choice branch).1 hLattice hBox hNext
            (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2 hPosition.2
          have hLength := choice.select_progress branch
          rw [hw,← selectWithWork_erasure] at hLength
          have hLaterPosition := BinaryPRGWordControllerBooleanResourceLoop.run_position seed capacity n hCount hC
            (selectWithWork choice branch).1 (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2 hPosition.2
          rw [← run_erasure] at hLaterPosition
          have hSpan :
            (run seed capacity n hCount hC (selectWithWork choice branch).1
              (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2 hPosition.2).1.2.value - pc.value =
              ((BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2.value - pc.value) +
              ((run seed capacity n hCount hC (selectWithWork choice branch).1
                (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2 hPosition.2).1.2.value -
                  (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2.value) := by omega
          rw [hSpan]
          unfold bound pairBound at ih ⊢
          nlinarith
termination_by state.state.active.length
decreasing_by
  rw [selectWithWork_erasure]
  have hw := prepared_state state choice ((prepareWithWork_erasure capacity n hCount hC state).symm.trans hPrepared)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_completed_invariant (D : ℕ) (seed : BinarySeedLookupTree.Store)
    (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount)
    (hLattice : ∀ j,OnRationalLattice D (value ((table capacity.cap capacity.tree n hCount).read j)))
    (hs : StateInvariant (table capacity.cap capacity.tree n hCount) D state.reference)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (result : Certified capacity n hCount) (hSuccess : (run seed capacity n hCount hC state pc hp).1.1 = some result) :
    StateInvariant (table capacity.cap capacity.tree n hCount) D result.reference := by
  unfold run at hSuccess
  dsimp only at hSuccess
  split at hSuccess
  · rename_i finished hPrepared
    cases hSuccess
    have he := prepared_done_state state result ((prepareWithWork_erasure capacity n hCount hC state).symm.trans hPrepared)
    rw [he]
    exact hs
  · rename_i choice hPrepared
    have hw := prepared_state state choice ((prepareWithWork_erasure capacity n hCount hC state).symm.trans hPrepared)
    have hChoice : StateInvariant (table capacity.cap capacity.tree n hCount) D choice.state.reference := hw.symm ▸ hs
    split at hSuccess
    · cases hSuccess
    · rename_i branch hCoin
      have hNext := choice_select_invariant choice.original.original D hLattice hChoice branch
      rw [← choice.original.select_original,← choice.select_original,← selectWithWork_erasure] at hNext
      exact run_completed_invariant D seed capacity n hCount hC (selectWithWork choice branch).1 hLattice hNext
        (BinaryWordIndexCoinController.sample seed choice.probability pc hp).1.2
        (BinaryWordIndexCoinController.sample_position_bounds seed choice.probability pc hp).2 result hSuccess

termination_by state.state.active.length
decreasing_by
  rw [selectWithWork_erasure]
  have hw := prepared_state state _ ((prepareWithWork_erasure capacity n hCount hC state).symm.trans (by assumption))
  rw [← hw]
  exact Choice.select_progress _ _

end Blotto.BinaryPRGWordControllerBooleanResourceLoopWork
