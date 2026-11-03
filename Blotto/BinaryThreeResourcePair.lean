import Blotto.BinaryThreeResourceState
import Blotto.BinaryRationalPairProgram
import Blotto.BinaryStoredRationalCoin

/-! Actual resource-pair preparation and selected Boolean updates preserve the
retained active-resource state. Interior proofs are erased; the seven-opcode
pair computation, stored-probability coin and selected two-write update are
native Boolean paths. Shared-cap multi-pair and terminal continuations remain
separate until composed. -/

namespace Blotto.BinaryThreeResourcePair
open BinaryRationalNormalization BinaryRationalEncoding BinaryThreeResourceState

structure Certified (capacity : FixedArrayTable 3 SignedWord) where
  state : State
  canonical : ∀ j, CanonicalWord (state.resource.read j)
  nodup : state.active.Nodup
  membership : ∀ j, j∈state.active ↔ 0<value (state.resource.read j) ∧ value (state.resource.read j)<value (capacity.read j)

noncomputable def Certified.reference {capacity : FixedArrayTable 3 SignedWord} (state : Certified capacity) :
    RationalActiveResources (fun j=>value (capacity.read j)) where
  resource := RationalResourceArray.ofAllocation (allocation state.state)
  active := state.state.active
  nodup := state.nodup
  membership := by intro j; rw [RationalResourceArray.allocation_ofAllocation]; exact state.membership j

def initial (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) : Certified capacity where
  state := BinaryThreeResourceState.initial capacity resource
  canonical := hR
  nodup := (List.nodup_finRange 3).filter _
  membership := by intro j; simp [BinaryThreeResourceState.initial,List.mem_finRange,fractional_iff capacity resource hC hR j]

theorem initial_reference (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) :
    (initial capacity resource hC hR).reference = RationalActiveResources.initial
      (fun j=>value (capacity.read j)) (fun j=>value (resource.read j)) := by
  cases he : RationalActiveResources.initial (fun j=>value (capacity.read j)) (fun j=>value (resource.read j)) with
  | mk r active hn hm =>
    have hResource : r = RationalResourceArray.ofAllocation (fun j=>value (resource.read j)) :=
      (congrArg RationalActiveResources.resource he).symm
    have hActive : active=(BinaryThreeResourceState.initial capacity resource).active := by
      rw [BinaryThreeResourceState.initial_active capacity resource hC hR]
      exact (congrArg RationalActiveResources.active he).symm
    subst r
    subst active
    rfl

def pairSource {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active=a::b::tail) : BinaryRationalPairProgram.Source where
  lengthI:=capacity.read a
  lengthJ:=capacity.read b
  resourceI:=state.state.resource.read a
  resourceJ:=state.state.resource.read b
  lengthI_canonical:=hC a
  lengthJ_canonical:=hC b
  resourceI_canonical:=state.canonical a
  resourceJ_canonical:=state.canonical b
  interiorI:=(state.membership a).mp (by simp [he])
  interiorJ:=(state.membership b).mp (by simp [he])

theorem pairSource_pair {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active=a::b::tail) :
    (pairSource hC state a b tail he).pair=state.reference.pair a b tail he := by
  have hEq : ∀ p q : RationalRoundingPair, p.lengthI=q.lengthI → p.lengthJ=q.lengthJ →
      p.resourceI=q.resourceI → p.resourceJ=q.resourceJ → p=q := by
    intro p q h1 h2 h3 h4
    cases p
    cases q
    simp only at h1 h2 h3 h4
    cases h1
    cases h2
    cases h3
    cases h4
    rfl
  apply hEq
  · rfl
  · rfl
  · change value (state.state.resource.read a)=(RationalResourceArray.ofAllocation (allocation state.state)).allocation a
    rw [RationalResourceArray.allocation_ofAllocation]
    rfl
  · change value (state.state.resource.read b)=(RationalResourceArray.ofAllocation (allocation state.state)).allocation b
    rw [RationalResourceArray.allocation_ofAllocation]
    rfl

def chosenWord (source : BinaryRationalPairProgram.Source) (upper : Bool) : SignedWord :=
  BinaryRationalRegisterProgram.read source.run (if upper then 8 else 7)

theorem chosenWord_canonical (source : BinaryRationalPairProgram.Source) (upper : Bool) : CanonicalWord (chosenWord source upper) :=
  source.run_canonical _

theorem chosenWord_value (source : BinaryRationalPairProgram.Source) (upper : Bool) :
    value (chosenWord source upper)=if upper then source.pair.upper else source.pair.lower := by
  cases upper
  · exact source.run_lower
  · exact source.run_upper

def selectedState {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active=a::b::tail) (upper : Bool) : State :=
  BinaryThreeResourceState.update capacity state.state a b tail (chosenWord (pairSource hC state a b tail he) upper)

theorem selected_allocation {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active=a::b::tail) (upper : Bool) :
    allocation (selectedState hC state a b tail he upper) =
      (state.reference.update a b tail he (if upper then (state.reference.pair a b tail he).upper else
        (state.reference.pair a b tail he).lower)).resource.allocation := by
  rw [selectedState,update_allocation capacity state.state a b tail _ state.canonical (chosenWord_canonical _ upper),
    chosenWord_value,pairSource_pair]
  change Function.update (Function.update (allocation state.state) a _) b _ =
    (state.reference.resource.updatePair a b _).allocation
  rw [RationalResourceArray.allocation_updatePair]
  simp only [Certified.reference,RationalResourceArray.allocation_ofAllocation]

theorem selected_active {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active=a::b::tail) (upper : Bool) :
    (selectedState hC state a b tail he upper).active =
      (state.reference.update a b tail he (if upper then (state.reference.pair a b tail he).upper else
        (state.reference.pair a b tail he).lower)).active := by
  rw [selectedState,update_active capacity state.state a b tail _ hC state.canonical (chosenWord_canonical _ upper)]
  change _ = rationalRetainedPair (fun j=>value (capacity.read j))
    (state.reference.resource.updatePair a b _) a b ++ tail
  unfold rationalRetainedPair
  rw [rationalFractionalAt_function]
  have hAllocation := selected_allocation hC state a b tail he upper
  change allocation (BinaryThreeResourceState.update capacity state.state a b tail _) =
    (state.reference.resource.updatePair a b _).allocation at hAllocation
  rw [hAllocation]

def selected {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active=a::b::tail) (upper : Bool) : Certified capacity :=
  let next:=selectedState hC state a b tail he upper
  { state:=next
    canonical:=update_canonical capacity state.state a b tail _ state.canonical (chosenWord_canonical _ upper)
    nodup:=by
      rw [selected_active hC state a b tail he upper]
      exact (state.reference.update a b tail he (if upper then (state.reference.pair a b tail he).upper else
        (state.reference.pair a b tail he).lower)).nodup
    membership:=by
      intro j
      rw [selected_active hC state a b tail he upper]
      have hm:=(state.reference.update a b tail he (if upper then (state.reference.pair a b tail he).upper else
        (state.reference.pair a b tail he).lower)).membership j
      have ha:=selected_allocation hC state a b tail he upper
      rw [←ha] at hm
      exact hm }

theorem resourceArray_ext (a b : RationalResourceArray 3) (h : a.allocation=b.allocation) : a=b := by
  cases a with
  | mk first hFirst =>
    cases b with
    | mk second hSecond =>
      have he : first=second := by
        apply Array.ext
        · omega
        · intro j hj hk
          have hJ : j<3 := by omega
          exact congrFun h ⟨j,hJ⟩
      subst second
      rfl

theorem selected_reference {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active=a::b::tail) (upper : Bool) :
    (selected hC state a b tail he upper).reference =
      state.reference.update a b tail he (if upper then (state.reference.pair a b tail he).upper else
        (state.reference.pair a b tail he).lower) := by
  have ha:=selected_allocation hC state a b tail he upper
  have ht:=selected_active hC state a b tail he upper
  cases hr : state.reference.update a b tail he (if upper then (state.reference.pair a b tail he).upper else
        (state.reference.pair a b tail he).lower) with
  | mk resource active hn hm =>
      rw [hr] at ha ht
      have hResource : resource=RationalResourceArray.ofAllocation (allocation (selectedState hC state a b tail he upper)) := by
        apply resourceArray_ext
        rw [RationalResourceArray.allocation_ofAllocation]
        exact ha.symm
      have hActive : active=(selectedState hC state a b tail he upper).active := ht.symm
      subst resource
      subst active
      rfl

theorem selected_progress {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active=a::b::tail) (upper : Bool) :
    (selected hC state a b tail he upper).state.active.length < state.state.active.length := by
  have hp:=state.reference.update_length_lt a b tail he
    (z:=if upper then (state.reference.pair a b tail he).upper else (state.reference.pair a b tail he).lower)
    (by cases upper; exact Or.inl rfl; exact Or.inr rfl)
  rw [←selected_reference hC state a b tail he upper] at hp
  exact hp

end Blotto.BinaryThreeResourcePair
