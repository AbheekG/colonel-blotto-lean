import Blotto.BinaryPRGWordControllerPairOutputs
import Blotto.BinaryResourceChoice

/-! Reached pair choices retain exactly the three Boolean-register output
words. The old native SSA is a noncomputable proof view only. Resource table
updates are still the explicit original native backend. -/
namespace Blotto.BinaryPRGWordControllerThreeChoice
open BinaryRationalNormalization BinaryRationalEncoding BinaryThreeResourcePair
open BinaryPRGWordControllerPairOutputs

structure Choice (capacity : FixedArrayTable 3 SignedWord) (hC : ∀ j,CanonicalWord (capacity.read j)) where
  state : Certified capacity
  first : Fin 3
  second : Fin 3
  tail : List (Fin 3)
  head_pair : state.state.active = first :: second :: tail
  outputs : Outputs
  outputs_correct : outputs = prepare (pairSource hC state first second tail head_pair)

namespace Choice

def prepare {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3))
    (he : state.state.active = a :: b :: tail) : Choice capacity hC :=
  ⟨state,a,b,tail,he,BinaryPRGWordControllerPairOutputs.prepare (pairSource hC state a b tail he),rfl⟩

def endpoint {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : SignedWord :=
  if branch then choice.outputs.upper else choice.outputs.lower

def probability {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : SignedWord := choice.outputs.probability

noncomputable def original {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : BinaryResourceChoice.Choice capacity hC :=
  ⟨choice.state,choice.first,choice.second,choice.tail,choice.head_pair,
    (pairSource hC choice.state choice.first choice.second choice.tail choice.head_pair).run,rfl⟩

theorem endpoint_original {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : choice.endpoint branch = choice.original.endpoint branch := by
  unfold endpoint original BinaryResourceChoice.Choice.endpoint
  rw [choice.outputs_correct]
  cases branch
  · exact (prepare_words _).1
  · exact (prepare_words _).2.1

theorem probability_original {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : choice.probability = choice.original.probability := by
  unfold probability original BinaryResourceChoice.Choice.probability
  rw [choice.outputs_correct]
  exact (prepare_words _).2.2

theorem endpoint_eq {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : choice.endpoint branch =
      chosenWord (pairSource hC choice.state choice.first choice.second choice.tail choice.head_pair) branch :=
  (choice.endpoint_original branch).trans (choice.original.endpoint_eq branch)

def select {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : Certified capacity :=
  { state := BinaryThreeResourceState.update capacity choice.state.state choice.first choice.second choice.tail (choice.endpoint branch)
    canonical := by
      apply BinaryThreeResourceState.update_canonical _ _ _ _ _ _ choice.state.canonical
      rw [choice.endpoint_eq]
      exact chosenWord_canonical _ branch
    nodup := by
      rw [choice.endpoint_eq]
      exact (selected hC choice.state choice.first choice.second choice.tail choice.head_pair branch).nodup
    membership := by
      rw [choice.endpoint_eq]
      exact (selected hC choice.state choice.first choice.second choice.tail choice.head_pair branch).membership }

theorem select_original {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : choice.select branch = choice.original.select branch := by
  unfold select BinaryResourceChoice.Choice.select
  simp only [endpoint_original]
  rfl

theorem select_progress {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) :
    (choice.select branch).state.active.length < choice.state.state.active.length := by
  rw [choice.select_original]
  exact choice.original.select_progress branch

end Choice

inductive Preparation (capacity : FixedArrayTable 3 SignedWord) (hC : ∀ j,CanonicalWord (capacity.read j)) where
  | done (state : Certified capacity)
  | ask (choice : Choice capacity hC)

def prepare (capacity : FixedArrayTable 3 SignedWord) (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : Preparation capacity hC :=
  match he : state.state.active with
  | a :: b :: tail => .ask (Choice.prepare hC state a b tail he)
  | _ => .done state

noncomputable def Preparation.original {capacity : FixedArrayTable 3 SignedWord}
    {hC : ∀ j,CanonicalWord (capacity.read j)} : Preparation capacity hC → BinaryResourceChoice.Preparation capacity hC
  | .done state => .done state
  | .ask choice => .ask choice.original

theorem prepare_original (capacity : FixedArrayTable 3 SignedWord) (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : (prepare capacity hC state).original = BinaryResourceChoice.prepare capacity hC state := by
  cases state with
  | mk data canonical nodup membership =>
    cases data with
    | mk resource active =>
      cases active with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b tail => rfl

theorem prepared_state {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (state : Certified capacity) (choice : Choice capacity hC) (h : prepare capacity hC state = .ask choice) :
    choice.state = state := by
  unfold prepare at h
  split at h
  · cases h
    rfl
  · cases h

end Blotto.BinaryPRGWordControllerThreeChoice
