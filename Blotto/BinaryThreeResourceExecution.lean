import Blotto.BinaryThreeResourceHeight
import Blotto.BinaryGeneralResourceExecution
import Blotto.BinaryPRGPreparationWork

/-! Actual three-coordinate pair preparation and selected two-write updates
retain primitive arithmetic charges, logical accesses/control and conservative
copy allowances separately. Source heights price Boolean work; no compiler,
bookkeeping, ownership or allocator/GC bound is inferred. -/

namespace Blotto.BinaryThreeResourceExecution
open BinaryRationalNormalization BinaryRationalEncoding BinaryThreeResourcePair
open BinaryResourceChoice BinaryThreeResourceHeight BinaryGeneralResourceExecution
open scoped BigOperators

def prepareWithCharge {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active = a :: b :: tail) :
    Choice capacity hC × Charge :=
  let source := pairSource hC state a b tail he
  let registers := source.runWithWork
  (⟨state, a, b, tail, he, registers.1, (by
      change (BinaryRationalRegisterProgram.runWithWork RealPairProgram.code source.inputs).1 = source.run
      rw [BinaryRationalRegisterProgram.runWithWork_refines]; rfl)⟩,
    ⟨registers.2, 4, 0, 3, source.sourcePayloadWork⟩)

theorem prepareWithCharge_state {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active = a :: b :: tail) :
    (prepareWithCharge hC state a b tail he).1 = Choice.prepare hC state a b tail he := by
  unfold prepareWithCharge Choice.prepare
  simp only [BinaryRationalPairProgram.Source.runWithWork, BinaryRationalRegisterProgram.runWithWork_refines,
    BinaryRationalPairProgram.Source.run]

def pairBound (C s : ℕ) : ℕ :=
  let H := resourceHeight C s
  7 * (12000 * (32 * H + 32) ^ 3 + 28 * (64 * H + 63) + 4)

theorem prepareWithCharge_bound {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (state : Certified capacity) (h : StateHeight capacity C s state)
    (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active = a :: b :: tail) :
    (prepareWithCharge hC state a b tail he).2.booleanWork ≤ pairBound C s :=
  (pairSource hC state a b tail he).work_bound (pair_height hC C s hCap state h a b tail he)
    (hs.trans (expressionHeightBudget_ge_input s _))

def prepareStep {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) : Preparation capacity hC × Charge :=
  match he : state.state.active with
  | a :: b :: tail =>
      let result := prepareWithCharge hC state a b tail he
      (.ask result.1, result.2.add ⟨0,0,0,1,0⟩)
  | _ => (.done state, ⟨0,0,0,1,0⟩)

theorem prepareStep_state {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) : (prepareStep hC state).1 = BinaryResourceChoice.prepare capacity hC state := by
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
          dsimp only [prepareStep, BinaryResourceChoice.prepare]
          rw [prepareWithCharge_state]

theorem prepareStep_choice_state {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) (choice : Choice capacity hC) (hs : (prepareStep hC state).1 = .ask choice) :
    choice.state = state := by
  have hh := prepareStep_state hC state
  rw [hs] at hh
  unfold BinaryResourceChoice.prepare at hh
  split at hh
  · cases Preparation.ask.inj hh; rfl
  · cases hh

theorem prepareStep_bound {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (state : Certified capacity) (h : StateHeight capacity C s state) :
    (prepareStep hC state).2.booleanWork ≤ pairBound C s := by
  unfold prepareStep
  split
  · rename_i a b tail he
    simpa only [Charge.add, Nat.add_zero] using
      (BinaryThreeResourceExecution.prepareWithCharge_bound hC C s hs hCap state h a b tail he)
  · exact Nat.zero_le _

theorem prepareStep_done_work {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state result : Certified capacity) (hs : (prepareStep hC state).1 = .done result) :
    (prepareStep hC state).2.booleanWork = 0 := by
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
          dsimp only [prepareStep] at hs
          cases hs

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

def selectBound (C s : ℕ) : ℕ :=
  24000 * (2 + 2 * expressionHeightBudget (resourceHeight C s) 2) ^ 3 +
    2000 * (2 + 2 * resourceHeight C s) ^ 2

theorem selectWithCharge_bound {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (choice : Choice capacity hC) (h : StateHeight capacity C s choice.state) (branch : Bool) :
    (selectWithCharge choice branch).2.booleanWork ≤ selectBound C s := by
  let H := resourceHeight C s
  let W := 1 + 2 * expressionHeightBudget H 2
  have hPair := pair_height hC C s hCap choice.state h choice.first choice.second choice.tail choice.head_pair
  have hsH : 2 ≤ H := hs.trans (expressionHeightBudget_ge_input s _)
  have hEndpoint : RationalHeight (value (choice.endpoint branch)) (expressionHeightBudget H 2) := by
    rw [choice.endpoint_eq, BinaryThreeResourcePair.chosenWord_value]
    cases branch
    · exact (hPair.endpoints hsH).1
    · exact (hPair.endpoints hsH).2
  have hChosen : CanonicalWord (choice.endpoint branch) := by
    rw [choice.endpoint_eq]; exact chosenWord_canonical _ branch
  have hChosenW := hChosen.2.trans (rationalWordWidth_of_height hEndpoint)
  have hFirst := resource_width C s choice.state h choice.first
  have hSecond := resource_width C s choice.state h choice.second
  have hW : 1 + 2 * H ≤ W := Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input H 2)) 1
  have hAdd := BinaryPRGPreparationWork.operation_uniform_bound .add _ _ W (hFirst.trans hW) (hSecond.trans hW)
  have hTotalC := BinaryReflectedFourSetup.opcode_canonical .add _ _ (choice.state.canonical choice.first) (choice.state.canonical choice.second)
  have hTotalH : RationalHeight (value (BinaryRationalOpcode.apply .add (choice.state.state.resource.read choice.first)
      (choice.state.state.resource.read choice.second))) (expressionHeightBudget H 1) := by
    rw [BinaryRationalOpcode.apply_value .add _ _ (choice.state.canonical choice.first).1 (choice.state.canonical choice.second).1]
    have hi : RationalHeight (value (choice.state.state.resource.read choice.first)) (expressionHeightBudget H 0) := by
      simpa only [expressionHeightBudget_zero] using resource_height C s choice.state h choice.first
    have hj : RationalHeight (value (choice.state.state.resource.read choice.second)) (expressionHeightBudget H 0) := by
      simpa only [expressionHeightBudget_zero] using resource_height C s choice.state h choice.second
    exact hi.add_level hj
  have hTotalW : width (BinaryRationalOpcode.applyWithWork .add (choice.state.state.resource.read choice.first)
      (choice.state.state.resource.read choice.second)).1 ≤ W := by
    rw [BinaryRationalOpcode.applyWithWork_state]
    exact hTotalC.2.trans ((rationalWordWidth_of_height hTotalH).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_mono H (by decide : 1 ≤ 2))) 1))
  have hSub := BinaryPRGPreparationWork.operation_uniform_bound .sub _ _ W hTotalW hChosenW
  have hSelected := selected_height C s hs hCap choice h branch
  have hNextW := fun j => resource_width C s (choice.select branch) hSelected j
  have hCapsW := fun j => (hC j).2.trans (rationalWordWidth_of_height (capacity_height capacity C s hCap j))
  have hScan := (scanWithCharge_bound capacity (choice.select branch).state.resource [choice.first,choice.second]
    (1 + 2 * H) (by omega) hCapsW hNextW).1
  simp only [List.length_cons, List.length_nil] at hScan
  have hNext : (choice.state.state.resource.write choice.first (choice.endpoint branch)).write choice.second
      (BinaryRationalOpcode.applyWithWork .sub
        (BinaryRationalOpcode.applyWithWork .add (choice.state.state.resource.read choice.first)
          (choice.state.state.resource.read choice.second)).1 (choice.endpoint branch)).1 = (choice.select branch).state.resource := by
    simp only [BinaryRationalOpcode.applyWithWork_state]
    rfl
  unfold selectWithCharge
  dsimp only
  rw [hNext]
  unfold selectBound
  dsimp only [W,H] at hAdd hSub hScan
  nlinarith

end Blotto.BinaryThreeResourceExecution
