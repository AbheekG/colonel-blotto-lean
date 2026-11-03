import Blotto.BinarySharedResourceRun
import Blotto.RationalResourceHeightInvariant
import Blotto.RationalExpressionWordWidth

/-! Actual three-coordinate states carry rank-indexed source heights through
selected pair updates. The bound is used with C=2 for the reflected local phase;
it never replaces the lattice invariant of the general n-coordinate PRG loop.
Pending residual coins retain their original fixed stored width. -/

namespace Blotto.BinaryThreeResourceHeight
open BinaryRationalNormalization BinaryRationalEncoding BinaryThreeResourcePair
open BinaryResourceChoice

theorem reference_value {capacity : FixedArrayTable 3 SignedWord} (state : Certified capacity) (j : Fin 3) :
    state.reference.resource.allocation j = value (state.state.resource.read j) :=
  congrFun (RationalResourceArray.allocation_ofAllocation _) j

def heightRank {capacity : FixedArrayTable 3 SignedWord} (state : Certified capacity) : ℕ :=
  state.state.active.length - 1

def StateHeight (capacity : FixedArrayTable 3 SignedWord) (C s : ℕ) (state : Certified capacity) : Prop :=
  heightRank state ≤ C ∧ ∀ j, RationalHeight (value (state.state.resource.read j))
    (expressionHeightBudget s (3 * (C - heightRank state)))

def resourceHeight (C s : ℕ) : ℕ := expressionHeightBudget s (3 * C)
def coinWidth (C s : ℕ) : ℕ := 1 + 2 * expressionHeightBudget (resourceHeight C s) 4

theorem resource_height {capacity : FixedArrayTable 3 SignedWord} (C s : ℕ)
    (state : Certified capacity) (h : StateHeight capacity C s state) (j : Fin 3) :
    RationalHeight (value (state.state.resource.read j)) (resourceHeight C s) :=
  (h.2 j).mono (expressionHeightBudget_mono s (by omega))

theorem resource_width {capacity : FixedArrayTable 3 SignedWord} (C s : ℕ)
    (state : Certified capacity) (h : StateHeight capacity C s state) (j : Fin 3) :
    width (state.state.resource.read j) ≤ 1 + 2 * resourceHeight C s :=
  (state.canonical j).2.trans (rationalWordWidth_of_height (resource_height C s state h j))

theorem capacity_height (capacity : FixedArrayTable 3 SignedWord) (C s : ℕ)
    (h : ∀ j, RationalHeight (value (capacity.read j)) s) (j : Fin 3) :
    RationalHeight (value (capacity.read j)) (resourceHeight C s) :=
  (h j).mono (expressionHeightBudget_ge_input s _)

theorem pair_height {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (state : Certified capacity) (h : StateHeight capacity C s state)
    (a b : Fin 3) (tail : List (Fin 3)) (he : state.state.active = a :: b :: tail) :
    (pairSource hC state a b tail he).pair.FieldsHeight (resourceHeight C s) :=
  ⟨capacity_height capacity C s hCap a, capacity_height capacity C s hCap b,
    resource_height C s state h a, resource_height C s state h b⟩

theorem selected_rank_lt {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (branch : Bool) : heightRank (choice.select branch) < heightRank choice.state := by
  have hp := choice.select_progress branch
  have hLen : 2 ≤ choice.state.state.active.length := by rw [choice.head_pair]; simp only [List.length_cons]; omega
  unfold heightRank
  omega

theorem selected_height {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (choice : Choice capacity hC) (h : StateHeight capacity C s choice.state) (branch : Bool) :
    StateHeight capacity C s (choice.select branch) := by
  let depth := 3 * (C - heightRank choice.state)
  let H := expressionHeightBudget s depth
  have hsH : 2 ≤ H := hs.trans (expressionHeightBudget_ge_input s depth)
  have hCaps : ∀ j, RationalHeight (value (capacity.read j)) H :=
    fun j => (hCap j).mono (expressionHeightBudget_ge_input s depth)
  have hState : choice.state.reference.resource.HeightAt H := by
    intro j
    rw [reference_value]; exact h.2 j
  have hPair : (choice.state.reference.pair choice.first choice.second choice.tail choice.head_pair).FieldsHeight H := by
    rw [← pairSource_pair hC choice.state choice.first choice.second choice.tail choice.head_pair]
    exact ⟨hCaps _, hCaps _, h.2 _, h.2 _⟩
  have hEndpoint := hPair.endpoints hsH
  have hSelect : (choice.select branch).reference.resource.HeightAt (expressionHeightBudget H 3) := by
    rw [choice.select_reference]
    unfold ResourceChoice.select
    apply choice.state.reference.update_height H hsH hCaps hState choice.first choice.second choice.tail choice.head_pair
    cases branch
    · exact Or.inl choice.reference.lower_correct
    · exact Or.inr choice.reference.upper_correct
  have hRank := selected_rank_lt choice branch
  have hBudget := h.1
  refine ⟨by omega, ?_⟩
  intro j
  have hj := hSelect j
  rw [expressionHeightBudget_comp, reference_value] at hj
  exact hj.mono (expressionHeightBudget_mono s (show depth + 3 ≤ 3 * (C - heightRank (choice.select branch)) by dsimp only [depth]; omega))

theorem probability_width {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j, CanonicalWord (capacity.read j)}
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (choice : Choice capacity hC) (h : StateHeight capacity C s choice.state) : width choice.probability ≤ coinWidth C s := by
  let source := pairSource hC choice.state choice.first choice.second choice.tail choice.head_pair
  have hPair := pair_height hC C s hCap choice.state h choice.first choice.second choice.tail choice.head_pair
  have hp := hPair.probability (hs.trans (expressionHeightBudget_ge_input s _))
  have hCanonical := source.run_canonical 11
  have hValue := source.run_probability
  unfold Choice.probability
  rw [choice.registers_correct]
  rw [← hValue] at hp
  exact hCanonical.2.trans (rationalWordWidth_of_height hp)

theorem initial_height (capacity resource : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j))
    (s : ℕ) (hHeight : ∀ j, RationalHeight (value (resource.read j)) s) :
    StateHeight capacity 2 s (initial capacity resource hC hR) := by
  have hLen : (initial capacity resource hC hR).state.active.length ≤ 3 :=
    (List.length_filter_le _ _).trans_eq (by simp)
  refine ⟨by unfold heightRank; omega, ?_⟩
  intro j
  exact (hHeight j).mono (expressionHeightBudget_ge_input s _)

end Blotto.BinaryThreeResourceHeight
