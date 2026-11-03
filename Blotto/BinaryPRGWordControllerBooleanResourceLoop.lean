import Blotto.BinaryPRGWordControllerBooleanResourceInitial
import Blotto.BinaryPRGWordControllerBooleanResourcePair
import Blotto.BinaryPRGWordControllerResource

/-! The reached resource loop retains Boolean-address capacity/resource trees,
Boolean active identifiers and the original absolute Boolean seed counter.
Native Certified states are proof-only views. Pair preparation, selected
arithmetic, path-copy writes and fractional scans execute the checked Boolean
backends. Input/output materialization is a separately priced source join. -/
namespace Blotto.BinaryPRGWordControllerBooleanResourceLoop
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordStoreView
open BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourcePair
set_option maxHeartbeats 1000000

theorem capCanonical (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)) :
    ∀ j,CanonicalWord ((table capacity.cap capacity.tree n hCount).read j) :=
  view_canonical capacity n hCount (fun address h => hC ⟨address,h⟩)

structure Certified (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value) where
  state : State capacity.width capacity.cap
  certified : ∃ original : BinaryResourcePair.Certified (table capacity.cap capacity.tree n hCount),
    original.state = state.reference n hCount

noncomputable def Certified.reference {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    (state : Certified capacity n hCount) : BinaryResourcePair.Certified (table capacity.cap capacity.tree n hCount) :=
  state.certified.choose

theorem Certified.reference_state {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    (state : Certified capacity n hCount) : state.reference.state = state.state.reference n hCount :=
  state.certified.choose_spec

theorem native_ext {n : ℕ} {capacity : FixedArrayTable n SignedWord}
    (first second : BinaryResourcePair.Certified capacity) (h : first.state = second.state) : first = second := by
  cases first
  cases second
  cases h
  rfl

theorem Certified.canonical {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    (state : Certified capacity n hCount) (address : Address capacity.width capacity.cap) :
    CanonicalWord (lookup state.state.resource address.word) := by
  have h := state.reference.canonical (address.index n hCount)
  rw [state.reference_state] at h
  simpa only [State.reference,table_read] using h

theorem Certified.interior {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    (state : Certified capacity n hCount) : Interior capacity.tree state.state := by
  intro address hAddress
  have hm := (state.reference.membership (address.index n hCount)).mp (by
    rw [state.reference_state]
    exact List.mem_map.mpr ⟨address,hAddress,rfl⟩)
  rw [state.reference_state] at hm
  simpa only [State.reference,table_read] using hm

def initial (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (hCap : resource.cap = hWidth.symm ▸ capacity.cap) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (hR : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup (hWidth ▸ resource.tree) address.word)) :
    Certified capacity n hCount :=
  { state := BinaryPRGWordControllerBooleanResourceInitial.initial capacity resource hWidth hCap
    certified := by
      have hc := capCanonical capacity n hCount hC
      have hr := view_canonical (⟨capacity.width,capacity.cap,hWidth ▸ resource.tree⟩ : Store) n hCount
        (fun address h => hR ⟨address,h⟩)
      exact ⟨BinaryResourcePair.initial _ _ hc hr,
        (BinaryPRGWordControllerBooleanResourceInitial.initial_reference capacity resource hWidth hCap n hCount).symm⟩ }

theorem initial_reference (capacity resource : Store) (hWidth : resource.width = capacity.width)
    (hCap : resource.cap = hWidth.symm ▸ capacity.cap) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (hR : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup (hWidth ▸ resource.tree) address.word)) :
    (initial capacity resource hWidth hCap n hCount hC hR).reference =
      BinaryResourcePair.initial (table capacity.cap capacity.tree n hCount)
        (table capacity.cap (hWidth ▸ resource.tree) n hCount)
        (capCanonical capacity n hCount hC)
        (view_canonical (⟨capacity.width,capacity.cap,hWidth ▸ resource.tree⟩ : Store) n hCount
          (fun address h => hR ⟨address,h⟩)) := by
  apply native_ext
  rw [Certified.reference_state]
  exact BinaryPRGWordControllerBooleanResourceInitial.initial_reference capacity resource hWidth hCap n hCount

structure Choice (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)) where
  state : Certified capacity n hCount
  first : Address capacity.width capacity.cap
  second : Address capacity.width capacity.cap
  tail : List (Address capacity.width capacity.cap)
  head_pair : state.state.active = first :: second :: tail
  outputs : BinaryPRGWordControllerPairOutputs.Outputs
  outputs_correct : outputs = pair capacity.tree state.state first second tail hC state.canonical state.interior head_pair

namespace Choice

def prepare {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.state.active = first :: second :: tail) :
    Choice capacity n hCount hC :=
  ⟨state,first,second,tail,he,pair capacity.tree state.state first second tail hC state.canonical state.interior he,rfl⟩

def endpoint {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) (branch : Bool) : SignedWord :=
  if branch then choice.outputs.upper else choice.outputs.lower

def probability {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) : SignedWord := choice.outputs.probability

noncomputable def original {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) :
    BinaryPRGWordControllerGeneralChoice.Choice (table capacity.cap capacity.tree n hCount)
      (capCanonical capacity n hCount hC) :=
  { state := choice.state.reference
    first := choice.first.index n hCount
    second := choice.second.index n hCount
    tail := choice.tail.map (fun address => address.index n hCount)
    head_pair := by
      rw [choice.state.reference_state]
      simp only [State.reference,choice.head_pair,List.map_cons]
    outputs := choice.outputs
    outputs_correct := by
      rw [choice.outputs_correct]
      unfold pair
      congr 1
      exact source_reference capacity.tree choice.state.state choice.first choice.second choice.tail
        hC choice.state.canonical choice.state.interior choice.head_pair n hCount _
        choice.state.reference choice.state.reference_state }

theorem outputs_original {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) : choice.outputs = choice.original.outputs := rfl

theorem endpoint_original {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) (branch : Bool) : choice.endpoint branch = choice.original.endpoint branch := by
  simp only [endpoint,BinaryPRGWordControllerGeneralChoice.Choice.endpoint,outputs_original]

theorem probability_original {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) : choice.probability = choice.original.probability := by
  simp only [probability,BinaryPRGWordControllerGeneralChoice.Choice.probability,outputs_original]

theorem endpoint_canonical {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) (branch : Bool) : CanonicalWord (choice.endpoint branch) := by
  rw [choice.endpoint_original,choice.original.endpoint_eq]
  exact BinaryResourcePair.chosenWord_canonical _ _

def select {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) (branch : Bool) : Certified capacity n hCount :=
  { state := update capacity.tree choice.state.state choice.first choice.second choice.tail (choice.endpoint branch)
    certified := by
      refine ⟨choice.original.select branch,?_⟩
      have h := update_reference capacity.tree choice.state.state choice.first choice.second choice.tail
        (choice.endpoint branch) (choice.state.canonical choice.first).1 (choice.state.canonical choice.second).1
        (choice.endpoint_canonical branch).1 n hCount
      rw [← choice.state.reference_state,choice.endpoint_original] at h
      exact h.symm }

theorem select_original {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) (branch : Bool) : (choice.select branch).reference = choice.original.select branch := by
  apply native_ext
  rw [Certified.reference_state]
  have h := update_reference capacity.tree choice.state.state choice.first choice.second choice.tail
    (choice.endpoint branch) (choice.state.canonical choice.first).1 (choice.state.canonical choice.second).1
    (choice.endpoint_canonical branch).1 n hCount
  rw [← choice.state.reference_state,choice.endpoint_original] at h
  exact h

theorem select_progress {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity n hCount hC) (branch : Bool) :
    (choice.select branch).state.active.length < choice.state.state.active.length := by
  have h := choice.original.select_progress branch
  rw [← choice.select_original,Certified.reference_state] at h
  change ((choice.select branch).state.active.map _).length < (choice.state.reference.state.active).length at h
  rw [choice.state.reference_state] at h
  simpa only [State.reference,List.length_map] using h

end Choice

inductive Preparation (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)) where
  | done (state : Certified capacity n hCount)
  | ask (choice : Choice capacity n hCount hC)

def prepare (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) : Preparation capacity n hCount hC :=
  match he : state.state.active with
  | first :: second :: tail => .ask (Choice.prepare hC state first second tail he)
  | _ => .done state

noncomputable def Preparation.original {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)} :
    Preparation capacity n hCount hC → BinaryPRGWordControllerGeneralChoice.Preparation
      (table capacity.cap capacity.tree n hCount) (capCanonical capacity n hCount hC)
  | .done state => .done state.reference
  | .ask choice => .ask choice.original

theorem nativeChoice_ext {n : ℕ} {capacity : FixedArrayTable n SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)}
    (first second : BinaryPRGWordControllerGeneralChoice.Choice capacity hC)
    (hs : first.state = second.state) (hf : first.first = second.first) (hb : first.second = second.second)
    (ht : first.tail = second.tail) (ho : first.outputs = second.outputs) : first = second := by
  cases first
  cases second
  cases hs
  cases hf
  cases hb
  cases ht
  cases ho
  rfl

theorem prepare_original (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) : (prepare capacity n hCount hC state).original =
      BinaryPRGWordControllerGeneralChoice.prepare _ _ state.reference := by
  cases state with
  | mk data certified =>
    cases data with
    | mk tree addresses =>
      let state : Certified capacity n hCount := ⟨⟨tree,addresses⟩,certified⟩
      have hState := state.reference_state
      generalize hn : state.reference = native at hState ⊢
      cases native with
      | mk data canonical nodup membership =>
        cases data with
        | mk resource active =>
          have hResource := congrArg BinaryResourceState.State.resource hState
          have hActive := congrArg BinaryResourceState.State.active hState
          dsimp only [State.reference] at hResource hActive
          subst resource
          subst active
          change (prepare capacity n hCount hC state).original = _
          unfold prepare BinaryPRGWordControllerGeneralChoice.prepare
          cases addresses with
          | nil =>
            simp only [state,Preparation.original,hn]
            rfl
          | cons first rest =>
            cases rest with
            | nil =>
              simp only [state,Preparation.original,hn,List.map_cons,List.map_nil]
              rfl
            | cons second tail =>
              dsimp only [state,List.map_cons]
              apply congrArg BinaryPRGWordControllerGeneralChoice.Preparation.ask
              apply nativeChoice_ext
              · exact hn
              · rfl
              · rfl
              · rfl
              · change pair capacity.tree state.state first second tail hC state.canonical state.interior rfl = _
                unfold pair
                rw [source_reference capacity.tree state.state first second tail hC state.canonical state.interior rfl
                  n hCount _ _ state.reference_state]
                simp only [hn]
                rfl

theorem prepared_state {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (state : Certified capacity n hCount) (choice : Choice capacity n hCount hC)
    (h : prepare capacity n hCount hC state = .ask choice) : choice.state = state := by
  unfold prepare at h
  split at h
  · cases h
    rfl
  · cases h

theorem prepared_done_state {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (state result : Certified capacity n hCount) (h : prepare capacity n hCount hC state = .done result) : result = state := by
  unfold prepare at h
  split at h
  · cases h
  · cases h
    rfl

abbrev Result (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value) :=
  Option (Certified capacity n hCount) × FixedBinaryWord seed.width

def run (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Result seed capacity n hCount :=
  match _hs : prepare capacity n hCount hC state with
  | .done result => (some result,pc)
  | .ask choice =>
      let coin := BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp
      match coin.1 with
      | none => (none,coin.2)
      | some branch => run seed capacity n hCount hC (choice.select branch) coin.2
          (BinaryPRGWordControllerDataCoin.sample_position seed choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := prepared_state state choice _hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

noncomputable def Result.original {seed : BinarySeedLookupTree.Store} {capacity : Store} {n : ℕ}
    {hCount : n = capacity.cap.value} (result : Result seed capacity n hCount) :
    BinaryPRGWordControllerResource.Result seed (table capacity.cap capacity.tree n hCount) :=
  (result.1.map Certified.reference,result.2)

theorem run_original (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (run seed capacity n hCount hC state pc hp).original =
      BinaryPRGWordControllerResource.run seed (table capacity.cap capacity.tree n hCount)
        (capCanonical capacity n hCount hC) state.reference pc hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinaryPRGWordControllerResource.run
  rw [← prepare_original capacity n hCount hC state]
  dsimp only
  cases hs : prepare capacity n hCount hC state with
  | done result => rfl
  | ask choice =>
      dsimp only [Preparation.original]
      simp only [← choice.probability_original]
      cases hc : (BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp).1 with
      | none => rfl
      | some branch =>
          dsimp only
          rw [← choice.select_original]
          exact run_original seed capacity n hCount hC (choice.select branch)
            (BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp).2
            (BinaryPRGWordControllerDataCoin.sample_position seed choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := prepared_state state choice hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_position (seed : BinarySeedLookupTree.Store) (capacity : Store) (n : ℕ) (hCount : n = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    pc.value ≤ (run seed capacity n hCount hC state pc hp).2.value ∧
      (run seed capacity n hCount hC state pc hp).2.value ≤ seed.cap.value := by
  change pc.value ≤ (run seed capacity n hCount hC state pc hp).original.2.value ∧
    (run seed capacity n hCount hC state pc hp).original.2.value ≤ seed.cap.value
  rw [run_original]
  exact BinaryPRGWordControllerResource.run_position _ _ _ _ _ _

end Blotto.BinaryPRGWordControllerBooleanResourceLoop
