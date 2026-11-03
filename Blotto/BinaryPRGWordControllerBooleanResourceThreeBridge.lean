import Blotto.BinaryPRGWordControllerBooleanResourceSourceWork
import Blotto.BinaryPRGWordControllerThreeResource

/-! The native general resource implementation at dimension three and the
native three-resource implementation use the same stored cells, active list,
pair program and selected update. These concrete conversions preserve that
data and commute with preparation and the complete absolute Boolean cursor
run. The Boolean-tree source obtains its three-resource view through the
already checked native reference; no refinement assumption is supplied. -/

namespace Blotto.BinaryPRGWordControllerBooleanResourceThreeBridge
open BinaryRationalNormalization BinaryRationalEncoding

def generalState_toThree (state : BinaryResourceState.State 3) : BinaryThreeResourceState.State :=
  ⟨state.resource,state.active⟩

def threeState_toGeneral (state : BinaryThreeResourceState.State) : BinaryResourceState.State 3 :=
  ⟨state.resource,state.active⟩

theorem generalState_roundtrip (state : BinaryResourceState.State 3) :
    threeState_toGeneral (generalState_toThree state) = state := by
  cases state
  rfl

theorem threeState_roundtrip (state : BinaryThreeResourceState.State) :
    generalState_toThree (threeState_toGeneral state) = state := by
  cases state
  rfl

def generalCertified_toThree {capacity : FixedArrayTable 3 SignedWord}
    (state : BinaryResourcePair.Certified capacity) : BinaryThreeResourcePair.Certified capacity :=
  ⟨generalState_toThree state.state,state.canonical,state.nodup,state.membership⟩

def threeCertified_toGeneral {capacity : FixedArrayTable 3 SignedWord}
    (state : BinaryThreeResourcePair.Certified capacity) : BinaryResourcePair.Certified capacity :=
  ⟨threeState_toGeneral state.state,state.canonical,state.nodup,state.membership⟩

theorem generalCertified_state {capacity : FixedArrayTable 3 SignedWord}
    (state : BinaryResourcePair.Certified capacity) :
    (generalCertified_toThree state).state = generalState_toThree state.state := rfl

theorem threeCertified_state {capacity : FixedArrayTable 3 SignedWord}
    (state : BinaryThreeResourcePair.Certified capacity) :
    (threeCertified_toGeneral state).state = threeState_toGeneral state.state := rfl

theorem generalCertified_roundtrip {capacity : FixedArrayTable 3 SignedWord}
    (state : BinaryResourcePair.Certified capacity) :
    threeCertified_toGeneral (generalCertified_toThree state) = state := by
  cases state with
  | mk data canonical nodup membership => cases data; rfl

theorem threeCertified_roundtrip {capacity : FixedArrayTable 3 SignedWord}
    (state : BinaryThreeResourcePair.Certified capacity) :
    generalCertified_toThree (threeCertified_toGeneral state) = state := by
  cases state with
  | mk data canonical nodup membership => cases data; rfl

theorem generalCertified_reference {capacity : FixedArrayTable 3 SignedWord}
    (state : BinaryResourcePair.Certified capacity) :
    (generalCertified_toThree state).reference = state.reference := rfl

theorem threeCertified_reference {capacity : FixedArrayTable 3 SignedWord}
    (state : BinaryThreeResourcePair.Certified capacity) :
    (threeCertified_toGeneral state).reference = state.reference := rfl

theorem general_toThree_initial (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    generalCertified_toThree (BinaryResourcePair.initial capacity resource hC hR) =
      BinaryThreeResourcePair.initial capacity resource hC hR := rfl

theorem pairSource_toThree {capacity : FixedArrayTable 3 SignedWord}
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : BinaryResourcePair.Certified capacity)
    (first second : Fin 3) (tail : List (Fin 3)) (he : state.state.active = first :: second :: tail) :
    BinaryResourcePair.pairSource hC state first second tail he =
      BinaryThreeResourcePair.pairSource hC (generalCertified_toThree state) first second tail he := rfl

def choice_toThree {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : BinaryPRGWordControllerGeneralChoice.Choice capacity hC) :
    BinaryPRGWordControllerThreeChoice.Choice capacity hC :=
  ⟨generalCertified_toThree choice.state,choice.first,choice.second,choice.tail,
    choice.head_pair,choice.outputs,choice.outputs_correct⟩

def choice_toGeneral {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : BinaryPRGWordControllerThreeChoice.Choice capacity hC) :
    BinaryPRGWordControllerGeneralChoice.Choice capacity hC :=
  ⟨threeCertified_toGeneral choice.state,choice.first,choice.second,choice.tail,
    choice.head_pair,choice.outputs,choice.outputs_correct⟩

theorem choice_toThree_state {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : BinaryPRGWordControllerGeneralChoice.Choice capacity hC) :
    (choice_toThree choice).state = generalCertified_toThree choice.state := rfl

theorem choice_toThree_probability {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : BinaryPRGWordControllerGeneralChoice.Choice capacity hC) :
    (choice_toThree choice).probability = choice.probability := rfl

theorem choice_toThree_endpoint {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : BinaryPRGWordControllerGeneralChoice.Choice capacity hC) (branch : Bool) :
    (choice_toThree choice).endpoint branch = choice.endpoint branch := rfl

theorem choice_toThree_select {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : BinaryPRGWordControllerGeneralChoice.Choice capacity hC) (branch : Bool) :
    (choice_toThree choice).select branch = generalCertified_toThree (choice.select branch) := rfl

def preparation_toThree {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)} :
    BinaryPRGWordControllerGeneralChoice.Preparation capacity hC →
      BinaryPRGWordControllerThreeChoice.Preparation capacity hC
  | .done state => .done (generalCertified_toThree state)
  | .ask choice => .ask (choice_toThree choice)

theorem prepare_toThree (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : BinaryResourcePair.Certified capacity) :
    preparation_toThree (BinaryPRGWordControllerGeneralChoice.prepare capacity hC state) =
      BinaryPRGWordControllerThreeChoice.prepare capacity hC (generalCertified_toThree state) := by
  cases state with
  | mk data canonical nodup membership =>
    cases data with
    | mk resource active =>
      cases active with
      | nil => rfl
      | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second tail => rfl

def result_toThree (seed : BinarySeedLookupTree.Store) (capacity : FixedArrayTable 3 SignedWord)
    (drawn : BinaryPRGWordControllerResource.Result seed capacity) :
    BinaryPRGWordControllerThreeResource.Result seed capacity :=
  (drawn.1.map generalCertified_toThree,drawn.2)

theorem run_toThree (seed : BinarySeedLookupTree.Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : BinaryResourcePair.Certified capacity)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    result_toThree seed capacity (BinaryPRGWordControllerResource.run seed capacity hC state pc hp) =
      BinaryPRGWordControllerThreeResource.run seed capacity hC (generalCertified_toThree state) pc hp := by
  conv_lhs => unfold BinaryPRGWordControllerResource.run
  conv_rhs => unfold BinaryPRGWordControllerThreeResource.run
  rw [← prepare_toThree capacity hC state]
  dsimp only
  cases hs : BinaryPRGWordControllerGeneralChoice.prepare capacity hC state with
  | done result => rfl
  | ask choice =>
      dsimp only [preparation_toThree]
      simp only [choice_toThree_probability]
      cases hc : (BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp).1 with
      | none => rfl
      | some branch =>
          dsimp only
          rw [choice_toThree_select]
          exact run_toThree seed capacity hC (choice.select branch)
            (BinaryPRGWordControllerDataCoin.sample seed choice.probability pc hp).2
            (BinaryPRGWordControllerDataCoin.sample_position seed choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_toThree_position (seed : BinarySeedLookupTree.Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : BinaryResourcePair.Certified capacity)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.run seed capacity hC state pc hp).2 =
      (BinaryPRGWordControllerThreeResource.run seed capacity hC (generalCertified_toThree state) pc hp).2 :=
  congrArg Prod.snd (run_toThree seed capacity hC state pc hp)

theorem run_toThree_none (seed : BinarySeedLookupTree.Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : BinaryResourcePair.Certified capacity)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPRGWordControllerResource.run seed capacity hC state pc hp).1 = none ↔
      (BinaryPRGWordControllerThreeResource.run seed capacity hC (generalCertified_toThree state) pc hp).1 = none := by
  have h := congrArg Prod.fst (run_toThree seed capacity hC state pc hp)
  change Option.map generalCertified_toThree _ = _ at h
  rw [← h]
  simp only [Option.map_eq_none_iff]

theorem run_toGeneral (seed : BinarySeedLookupTree.Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : BinaryThreeResourcePair.Certified capacity)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((BinaryPRGWordControllerThreeResource.run seed capacity hC state pc hp).1.map threeCertified_toGeneral,
      (BinaryPRGWordControllerThreeResource.run seed capacity hC state pc hp).2) =
      BinaryPRGWordControllerResource.run seed capacity hC (threeCertified_toGeneral state) pc hp := by
  have h := run_toThree seed capacity hC (threeCertified_toGeneral state) pc hp
  rw [threeCertified_roundtrip] at h
  rw [← h]
  unfold result_toThree
  simp only [Option.map_map]
  have he : threeCertified_toGeneral ∘ generalCertified_toThree =
      (id : BinaryResourcePair.Certified capacity → BinaryResourcePair.Certified capacity) := by
    funext started
    exact generalCertified_roundtrip started
  rw [he,Option.map_id]
  rfl

theorem initialRun_toThree (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    result_toThree seed capacity (BinaryPRGWordControllerResource.initialRun seed capacity resource hC hR) =
      BinaryPRGWordControllerThreeResource.run seed capacity hC
        (BinaryThreeResourcePair.initial capacity resource hC hR) (BinaryWordIndexCoinController.zeroIndex seed)
        (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _) := by
  unfold BinaryPRGWordControllerResource.initialRun
  rw [run_toThree,general_toThree_initial]

open BinaryPRGWordControllerWordStore BinaryPRGWordControllerBooleanResourceUpdate
open BinaryPRGWordControllerBooleanResourceLoop

noncomputable def booleanState_toThree {capacity : Store} {hCount : 3 = capacity.cap.value}
    (state : Certified capacity 3 hCount) :
    BinaryThreeResourcePair.Certified (table capacity.cap capacity.tree 3 hCount) :=
  generalCertified_toThree state.reference

noncomputable def booleanChoice_toThree {capacity : Store} {hCount : 3 = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity 3 hCount hC) :
    BinaryPRGWordControllerThreeChoice.Choice (table capacity.cap capacity.tree 3 hCount)
      (capCanonical capacity 3 hCount hC) :=
  choice_toThree choice.original

theorem booleanChoice_toThree_state {capacity : Store} {hCount : 3 = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity 3 hCount hC) :
    (booleanChoice_toThree choice).state = generalCertified_toThree choice.state.reference := rfl

theorem booleanChoice_toThree_probability {capacity : Store} {hCount : 3 = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity 3 hCount hC) :
    (booleanChoice_toThree choice).probability = choice.probability :=
  choice.probability_original.symm

theorem booleanChoice_toThree_endpoint {capacity : Store} {hCount : 3 = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity 3 hCount hC) (branch : Bool) :
    (booleanChoice_toThree choice).endpoint branch = choice.endpoint branch :=
  (choice.endpoint_original branch).symm

theorem booleanChoice_toThree_select {capacity : Store} {hCount : 3 = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity 3 hCount hC) (branch : Bool) :
    (booleanChoice_toThree choice).select branch = booleanState_toThree (choice.select branch) := by
  unfold booleanChoice_toThree booleanState_toThree
  rw [choice_toThree_select,choice.select_original]

theorem booleanChoice_toThree_source {capacity : Store} {hCount : 3 = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (choice : Choice capacity 3 hCount hC) :
    BinaryPRGWordControllerBooleanResourcePair.source capacity.tree choice.state.state
        choice.first choice.second choice.tail hC choice.state.canonical choice.state.interior choice.head_pair =
      BinaryThreeResourcePair.pairSource (capCanonical capacity 3 hCount hC) (booleanChoice_toThree choice).state
        (booleanChoice_toThree choice).first (booleanChoice_toThree choice).second
        (booleanChoice_toThree choice).tail (booleanChoice_toThree choice).head_pair := by
  rw [BinaryPRGWordControllerBooleanResourcePair.source_reference capacity.tree choice.state.state
    choice.first choice.second choice.tail hC choice.state.canonical choice.state.interior choice.head_pair
    3 hCount _ choice.state.reference choice.state.reference_state]
  rfl

theorem boolean_selected_height {capacity : Store} {hCount : 3 = capacity.cap.value}
    {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}
    (C s : ℕ) (hs : 2 ≤ s)
    (hCap : ∀ j,RationalHeight (value ((table capacity.cap capacity.tree 3 hCount).read j)) s)
    (choice : Choice capacity 3 hCount hC)
    (hState : BinaryThreeResourceHeight.StateHeight (table capacity.cap capacity.tree 3 hCount)
      C s (booleanState_toThree choice.state)) (branch : Bool) :
    BinaryThreeResourceHeight.StateHeight (table capacity.cap capacity.tree 3 hCount)
      C s (booleanState_toThree (choice.select branch)) := by
  have h := BinaryThreeResourceHeight.selected_height C s hs hCap (booleanChoice_toThree choice).original hState branch
  rw [← BinaryPRGWordControllerThreeChoice.Choice.select_original,booleanChoice_toThree_select] at h
  exact h

theorem booleanRun_toThree (seed : BinarySeedLookupTree.Store) (capacity : Store) (hCount : 3 = capacity.cap.value)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Certified capacity 3 hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    ((BinaryPRGWordControllerBooleanResourceLoop.run seed capacity 3 hCount hC state pc hp).1.map booleanState_toThree,
      (BinaryPRGWordControllerBooleanResourceLoop.run seed capacity 3 hCount hC state pc hp).2) =
      BinaryPRGWordControllerThreeResource.run seed (table capacity.cap capacity.tree 3 hCount)
        (capCanonical capacity 3 hCount hC) (booleanState_toThree state) pc hp := by
  unfold booleanState_toThree
  rw [← run_toThree seed _ _ state.reference pc hp,
    ← BinaryPRGWordControllerBooleanResourceLoop.run_original seed capacity 3 hCount hC state pc hp]
  unfold result_toThree Result.original
  simp only [Option.map_map]
  rfl

theorem sourceInitialRun_toThree (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    result_toThree seed capacity (BinaryPRGWordControllerBooleanResourceSource.initialRun seed capacity resource hC hR) =
      BinaryPRGWordControllerThreeResource.run seed capacity hC
        (BinaryThreeResourcePair.initial capacity resource hC hR) (BinaryWordIndexCoinController.zeroIndex seed)
        (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _) := by
  rw [BinaryPRGWordControllerBooleanResourceSource.initialRun_original,initialRun_toThree]

theorem sourceWorkInitialRun_toThree (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    result_toThree seed capacity (BinaryPRGWordControllerBooleanResourceSourceWork.initialRun seed capacity resource hC hR).1 =
      BinaryPRGWordControllerThreeResource.run seed capacity hC
        (BinaryThreeResourcePair.initial capacity resource hC hR) (BinaryWordIndexCoinController.zeroIndex seed)
        (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _) := by
  rw [BinaryPRGWordControllerBooleanResourceSourceWork.initialRun_erasure,initialRun_toThree]

end Blotto.BinaryPRGWordControllerBooleanResourceThreeBridge
