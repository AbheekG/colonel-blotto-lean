import Blotto.BinaryPRGWordControllerThreeChoice
import Blotto.BinaryPRGWordControllerPairOutputWork
import Blotto.BinaryThreeResourceExecution

/-! Preparation actually executes the Boolean-address pair backend. Selected
updates execute the retained native resource backend on the retained endpoint;
its price equality below compares the same operations on exactly equal operands.
The ghost old Choice is never called from executable preparation or selection. -/
namespace Blotto.BinaryPRGWordControllerThreeChoiceWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryThreeResourcePair
open BinaryPRGWordControllerThreeChoice BinaryGeneralResourceExecution

def prepareWithCharge {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3))
    (he : state.state.active = a :: b :: tail) : Choice capacity hC × Charge :=
  let source := pairSource hC state a b tail he
  let outputs := BinaryPRGWordControllerPairOutputs.prepareWithWork source
  (⟨state,a,b,tail,he,outputs.1,BinaryPRGWordControllerPairOutputs.prepareWithWork_erasure source⟩,
    ⟨outputs.2,4,0,3,source.sourcePayloadWork⟩)

theorem prepareWithCharge_state {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3))
    (he : state.state.active = a :: b :: tail) :
    (prepareWithCharge hC state a b tail he).1 = Choice.prepare hC state a b tail he := by
  unfold prepareWithCharge Choice.prepare
  simp only [BinaryPRGWordControllerPairOutputs.prepareWithWork_erasure]

def prepareStep {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : Preparation capacity hC × Charge :=
  match he : state.state.active with
  | a :: b :: tail =>
      let result := prepareWithCharge hC state a b tail he
      (.ask result.1,result.2.add ⟨0,0,0,1,0⟩)
  | _ => (.done state,⟨0,0,0,1,0⟩)

theorem prepareStep_state {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) : (prepareStep hC state).1 = BinaryPRGWordControllerThreeChoice.prepare capacity hC state := by
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
          dsimp only [prepareStep,BinaryPRGWordControllerThreeChoice.prepare]
          rw [prepareWithCharge_state]

theorem prepareStep_choice_state {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j,CanonicalWord (capacity.read j))
    (state : Certified capacity) (choice : Choice capacity hC) (h : (prepareStep hC state).1 = .ask choice) :
    choice.state = state :=
  BinaryPRGWordControllerThreeChoice.prepared_state state choice ((prepareStep_state hC state).symm.trans h)

def selectWithCharge {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : Certified capacity × Charge :=
  let chosen := choice.endpoint branch
  let first := choice.state.state.resource.read choice.first
  let second := choice.state.state.resource.read choice.second
  let total := BinaryRationalOpcode.applyWithWork .add first second
  let other := BinaryRationalOpcode.applyWithWork .sub total.1 chosen
  let next := (choice.state.state.resource.write choice.first chosen).write choice.second other.1
  let scan := scanWithCharge capacity next [choice.first,choice.second]
  let nextState : BinaryThreeResourceState.State := ⟨next, scan.1 ++ choice.tail⟩
  have hState : nextState = (choice.select branch).state := by
    unfold nextState Choice.select BinaryThreeResourceState.update
    dsimp only [next,scan,other,total,first,second,chosen]
    simp only [BinaryRationalOpcode.applyWithWork_state, scanWithCharge_state]
    rfl
  (⟨nextState, (by rw [hState]; exact (choice.select branch).canonical),
    (by rw [hState]; exact (choice.select branch).nodup),
    (by rw [hState]; exact (choice.select branch).membership)⟩,
    ⟨total.2 + other.2 + scan.2.booleanWork, 3 + scan.2.reads, 2, scan.2.listControl + 5,
      writeCopyAllowance choice.state.state.resource chosen +
        writeCopyAllowance (choice.state.state.resource.write choice.first chosen) other.1⟩)

theorem selectWithCharge_state {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : (selectWithCharge choice branch).1 = choice.select branch := by
  unfold selectWithCharge
  dsimp only
  unfold Choice.select BinaryThreeResourceState.update
  simp only [BinaryRationalOpcode.applyWithWork_state, scanWithCharge_state]
  rfl

/-- The unchanged selected native update has exactly the same operands and
source operations; this equality does not price the new pair interpreter. -/
theorem selectWithCharge_original {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) :
    selectWithCharge choice branch = BinaryThreeResourceExecution.selectWithCharge choice.original branch := by
  unfold selectWithCharge BinaryThreeResourceExecution.selectWithCharge
  dsimp only
  simp only [Choice.endpoint_original]
  rfl

end Blotto.BinaryPRGWordControllerThreeChoiceWork
