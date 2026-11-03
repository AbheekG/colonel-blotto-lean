import Blotto.BinaryGeneralResourceRun
import Blotto.WordMachineFallback

/-! A source-free deterministic resource fallback follows only the lower
selected endpoint, including a probability-one coin. It executes the actual
seven-opcode pair and two writes, without sampling or constructing both states.
The pair counter is structural; at most n−1 pairs are needed for n fields. -/

namespace Blotto.BinaryGeneralResourceFallback
variable {n : ℕ}
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourcePair BinaryGeneralResourceChoice
open scoped BigOperators

theorem prepare_owner {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (choice : Choice capacity hC)
    (h : BinaryGeneralResourceChoice.prepare capacity hC state=.ask choice) : choice.state=state:=by
  unfold BinaryGeneralResourceChoice.prepare at h
  split at h
  · cases Preparation.ask.inj h
    rfl
  · cases h

def chooseWithPairs {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : Certified capacity×ℕ:=
  match hp : BinaryGeneralResourceChoice.prepare capacity hC state with
  | .done result=>(result,0)
  | .ask choice=>
      let result:=chooseWithPairs hC (choice.select false)
      (result.1,result.2+1)
termination_by state.state.active.length
decreasing_by
  have h:=choice.select_progress false
  rw [prepare_owner hC state choice hp] at h
  exact h

def choose {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : Certified capacity:=(chooseWithPairs hC state).1

theorem choose_materialize {n : ℕ} {L : Fin n→ℚ} (cursor : RationalResourceCursor L) :
    (rationalResourceMachine L).chooseLeaf cursor=
      (rationalResourceMachine L).chooseLeaf (.ready cursor.materialize):=by
  conv_lhs=>unfold WordStateMachine.chooseLeaf
  conv_rhs=>unfold WordStateMachine.chooseLeaf
  rfl

theorem choose_refines {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : (choose hC state).reference=
      (rationalResourceMachine (fun j=>value (capacity.read j))).chooseLeaf (.ready state.reference):=by
  unfold choose
  conv_lhs=>unfold chooseWithPairs
  conv_rhs=>unfold WordStateMachine.chooseLeaf
  have hp:=BinaryGeneralResourceChoice.prepare_refines capacity hC state
  cases he : BinaryGeneralResourceChoice.prepare capacity hC state with
  | done result=>
      rw [he] at hp
      change rationalResourceStepReference state.reference=.done result.reference at hp
      rw [show (rationalResourceMachine (fun j=>value (capacity.read j))).step (.ready state.reference)=.done result.reference from
        (rationalResourceStep_refines state.reference).trans hp]
  | ask choice=>
      rw [he] at hp
      have hs : (rationalResourceMachine (fun j=>value (capacity.read j))).step (.ready state.reference)=
          .ask (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.numerator
            (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator
            (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator_pos
            (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.normalized
            (choice.reference.successor true) (choice.reference.successor false):=
        (rationalResourceStep_refines state.reference).trans hp
      rw [hs]
      have ih:=choose_refines hC (choice.select false)
      have hm:=choose_materialize (choice.reference.successor false)
      rw [←ResourceChoice.select_eq_materialize,←choice.select_reference false] at hm
      exact ih.trans hm.symm
termination_by state.state.active.length
decreasing_by
  have h:=choice.select_progress false
  rw [prepare_owner hC state choice he] at h
  exact h

theorem choose_pairs {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : (chooseWithPairs hC state).2≤state.state.active.length-1:=by
  conv_lhs=>unfold chooseWithPairs
  cases he : BinaryGeneralResourceChoice.prepare capacity hC state with
  | done result=>exact Nat.zero_le _
  | ask choice=>
      have ih:=choose_pairs hC (choice.select false)
      have ht:=choice.select_progress false
      rw [prepare_owner hC state choice he] at ht
      have hLength : 2≤state.state.active.length:=by
        have hHead:=choice.head_pair
        rw [prepare_owner hC state choice he] at hHead
        rw [hHead]
        simp only [List.length_cons]
        omega
      dsimp only
      omega
termination_by state.state.active.length
decreasing_by
  have h:=choice.select_progress false
  rw [prepare_owner hC state choice he] at h
  exact h


theorem choose_pairs_le_dimension {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : (chooseWithPairs hC state).2≤n-1:=by
  have h:=choose_pairs hC state
  have ht:=BinaryGeneralResourceRun.active_length_le state
  omega

theorem choose_terminal {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : (choose hC state).state.active.length≤1:=by
  have hl:=(rationalResourceMachine (fun j=>value (capacity.read j))).specification_forLeaves
    (fun _=>True) (fun result=>result.active.length≤1) (by
      intro cursor _
      have ht:=rationalResourceStep_terminal cursor.materialize
      unfold rationalResourceMachine rationalResourceTransition
      dsimp only
      cases hs : rationalResourceStep cursor.materialize with
      | done result=>rw [hs] at ht; exact ht
      | ask _ _ _ _ _ _=>trivial) (.ready state.reference) trivial
  have ht:=(rationalResourceMachine (fun j=>value (capacity.read j))).chooseLeaf_forLeaves
    (.ready state.reference) (fun result=>result.active.length≤1) hl
  rw [←choose_refines hC state] at ht
  exact ht

theorem choose_invariant {capacity : FixedArrayTable n SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (total : ℝ)
    (hs : RationalResourceInvariant (fun j=>value (capacity.read j)) total state.reference) :
    RationalResourceInvariant (fun j=>value (capacity.read j)) total (choose hC state).reference:=by
  have hl:=(rationalResourceMachine (fun j=>value (capacity.read j))).specification_forLeaves
    (fun cursor=>RationalResourceInvariant (fun j=>value (capacity.read j)) total cursor.materialize)
    (RationalResourceInvariant (fun j=>value (capacity.read j)) total) (by
      intro cursor hi
      have hc:=rationalResourceStep_invariant total cursor.materialize hi
      unfold rationalResourceMachine rationalResourceTransition
      dsimp only
      cases he : rationalResourceStep cursor.materialize with
      | done result=>rw [he] at hc; exact hc
      | ask _ _ _ _ _ _=>rw [he] at hc; exact hc) (.ready state.reference) hs
  have ht:=(rationalResourceMachine (fun j=>value (capacity.read j))).chooseLeaf_forLeaves
    (.ready state.reference) (RationalResourceInvariant (fun j=>value (capacity.read j)) total) hl
  rw [←choose_refines hC state] at ht
  exact ht

end Blotto.BinaryGeneralResourceFallback
