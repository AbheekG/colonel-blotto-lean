import Blotto.BinaryResourcePair
import Blotto.BinaryResourceChoice
import Blotto.SharedResourceRefinement
import Blotto.ProbabilityWordBitCost

/-! A native pending resource choice retains one Boolean state and the actual
pair registers. Numeric successors/coin words are proof references only. -/

namespace Blotto.BinaryGeneralResourceChoice
variable {n : ℕ}
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourceState BinaryResourcePair

structure Choice (capacity : FixedArrayTable n SignedWord) (hC : ∀ j, CanonicalWord (capacity.read j)) where
  state : Certified capacity
  first : Fin n
  second : Fin n
  tail : List (Fin n)
  head_pair : state.state.active=first::second::tail
  registers : Array SignedWord
  registers_correct : registers=(pairSource hC state first second tail head_pair).run

namespace Choice

def prepare {capacity : FixedArrayTable n SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail) : Choice capacity hC :=
  ⟨state,a,b,tail,he,(pairSource hC state a b tail he).run,rfl⟩

def endpoint {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : SignedWord :=
  BinaryRationalRegisterProgram.read choice.registers (if branch then 8 else 7)

def probability {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : SignedWord := BinaryRationalRegisterProgram.read choice.registers 11

theorem endpoint_eq {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : choice.endpoint branch =
      chosenWord (pairSource hC choice.state choice.first choice.second choice.tail choice.head_pair) branch := by
  unfold endpoint chosenWord
  rw [choice.registers_correct]

theorem probability_numbers {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) :
    BinaryBigEndian.littleValue choice.probability.numerator=(choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.numerator ∧
      BinaryBigEndian.littleValue choice.probability.denominator=(choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator := by
  unfold probability
  rw [choice.registers_correct]
  rw [←pairSource_pair hC choice.state choice.first choice.second choice.tail choice.head_pair]
  exact BinaryResourceChoice.Choice.source_probability_numbers _

def select {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : Certified capacity :=
  { state:=BinaryResourceState.update capacity choice.state.state choice.first choice.second choice.tail (choice.endpoint branch)
    canonical:=by
      apply update_canonical _ _ _ _ _ _ choice.state.canonical
      rw [choice.endpoint_eq]
      exact chosenWord_canonical _ branch
    nodup:=by
      rw [choice.endpoint_eq]
      exact (selected hC choice.state choice.first choice.second choice.tail choice.head_pair branch).nodup
    membership:=by
      rw [choice.endpoint_eq]
      exact (selected hC choice.state choice.first choice.second choice.tail choice.head_pair branch).membership }

theorem select_eq {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : choice.select branch =
      selected hC choice.state choice.first choice.second choice.tail choice.head_pair branch := by
  unfold select
  simp only [endpoint_eq]
  rfl

theorem select_progress {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : (choice.select branch).state.active.length<choice.state.state.active.length := by
  rw [choice.select_eq]
  exact selected_progress hC _ _ _ _ _ branch

noncomputable def reference {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) : ResourceChoice (fun j=>value (capacity.read j)) where
  state:=choice.state.reference
  first:=choice.first
  second:=choice.second
  tail:=choice.tail
  head_pair:=choice.head_pair
  lower:=value (choice.endpoint false)
  upper:=value (choice.endpoint true)
  lower_correct:=by rw [choice.endpoint_eq,chosenWord_value,pairSource_pair]; rfl
  upper_correct:=by rw [choice.endpoint_eq,chosenWord_value,pairSource_pair]; rfl

theorem select_reference {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : (choice.select branch).reference=choice.reference.select branch := by
  rw [choice.select_eq,selected_reference]
  unfold ResourceChoice.select reference
  simp only [endpoint_eq,chosenWord_value,pairSource_pair]
  cases branch <;> rfl

theorem successor_reference {capacity : FixedArrayTable n SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : choice.reference.successor branch =
      .selected choice.state.reference choice.first choice.second choice.tail choice.head_pair
        (if branch then (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).upper else
          (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).lower) := by
  unfold ResourceChoice.successor reference
  simp only [endpoint_eq,chosenWord_value,pairSource_pair]
  cases branch <;> rfl

end Choice

inductive Preparation (capacity : FixedArrayTable n SignedWord) (hC : ∀ j, CanonicalWord (capacity.read j)) where
  | done (state : Certified capacity)
  | ask (choice : Choice capacity hC)

def prepare (capacity : FixedArrayTable n SignedWord) (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) : Preparation capacity hC :=
  match he : state.state.active with
  | a::b::tail => .ask (Choice.prepare hC state a b tail he)
  | _ => .done state

theorem prepare_refines (capacity : FixedArrayTable n SignedWord) (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) :
    match prepare capacity hC state with
    | .done result => rationalResourceStepReference state.reference=.done result.reference
    | .ask choice => rationalResourceStepReference state.reference=.ask
        (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.numerator
        (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator
        (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.denominator_pos
        (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).words.normalized
        (choice.reference.successor true) (choice.reference.successor false) := by
  cases state with
  | mk data canonical nodup membership =>
      cases data with
      | mk resource active =>
          cases active with
          | nil => rfl
          | cons a rest =>
              cases rest with
              | nil => rfl
              | cons b tail =>
                  dsimp only [prepare,Choice.prepare]
                  rw [Choice.successor_reference,Choice.successor_reference]
                  rfl

end Blotto.BinaryGeneralResourceChoice
