import Blotto.BinaryResourceFallback
import Blotto.BinaryReflectedResourceWork

/-! The measured deterministic resource fallback follows exactly the lower
selected endpoint, including probability-one choices. It retains each actual
pair program/update charge and structural height credit. Original reflected
fields derive the setup scan and complete lower-path primitive bound. -/

namespace Blotto.BinaryThreeResourceFallbackWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryThreeResourcePair BinaryResourceChoice
open BinaryThreeResourceExecution BinaryThreeResourceHeight BinaryGeneralResourceExecution BinaryReflectedFourSetup

def chooseWithCharge {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) : Certified capacity × Charge :=
  let prepared := prepareStep hC state
  match _he : prepared.1 with
  | .done result => (result,prepared.2)
  | .ask choice =>
      let selected := BinaryThreeResourceExecution.selectWithCharge choice false
      let later := chooseWithCharge hC selected.1
      (later.1,prepared.2.add (selected.2.add later.2))
termination_by state.state.active.length
decreasing_by
  rw [BinaryThreeResourceExecution.selectWithCharge_state]
  have h := choice.select_progress false
  rw [prepareStep_choice_state hC state choice _he] at h
  exact h

theorem chooseWithCharge_state {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (state : Certified capacity) : (chooseWithCharge hC state).1 = BinaryResourceFallback.choose hC state := by
  conv_lhs => unfold chooseWithCharge
  unfold BinaryResourceFallback.choose
  conv_rhs => unfold BinaryResourceFallback.chooseWithPairs
  rw [← prepareStep_state hC state]
  dsimp only
  cases he : (prepareStep hC state).1 with
  | done result => rfl
  | ask choice =>
      dsimp only
      rw [BinaryThreeResourceExecution.selectWithCharge_state]
      exact chooseWithCharge_state hC (choice.select false)
termination_by state.state.active.length
decreasing_by
  have h := choice.select_progress false
  rw [prepareStep_choice_state hC state choice he] at h
  exact h

def pairBound (C s : ℕ) : ℕ := BinaryThreeResourceExecution.pairBound C s + BinaryThreeResourceExecution.selectBound C s

theorem chooseWithCharge_bound {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (state : Certified capacity) (hH : StateHeight capacity C s state) :
    (chooseWithCharge hC state).2.booleanWork ≤ heightRank state * pairBound C s := by
  conv_lhs => unfold chooseWithCharge
  dsimp only
  cases he : (prepareStep hC state).1 with
  | done result =>
      dsimp only
      rw [prepareStep_done_work hC state result he]
      exact Nat.zero_le _
  | ask choice =>
      dsimp only [Charge.add]
      have hState := prepareStep_choice_state hC state choice he
      have hChoice : StateHeight capacity C s choice.state := hState.symm ▸ hH
      have hPrepare := prepareStep_bound hC C s hs hCap state hH
      have hSelect := selectWithCharge_bound C s hs hCap choice hChoice false
      have hNext := selected_height C s hs hCap choice hChoice false
      have hRank := selected_rank_lt choice false
      rw [hState] at hRank
      rw [BinaryThreeResourceExecution.selectWithCharge_state]
      have hLater := chooseWithCharge_bound hC C s hs hCap (choice.select false) hNext
      have hScale := Nat.mul_le_mul_right (pairBound C s) (show heightRank (choice.select false) + 1 ≤ heightRank state by omega)
      unfold pairBound at *
      nlinarith
termination_by state.state.active.length
decreasing_by
  have h := choice.select_progress false
  rw [prepareStep_choice_state hC state choice he] at h
  exact h

theorem chooseWithCharge_height {capacity : FixedArrayTable 3 SignedWord} (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (state : Certified capacity) (hH : StateHeight capacity C s state) :
    StateHeight capacity C s (chooseWithCharge hC state).1 := by
  conv_rhs => unfold chooseWithCharge
  dsimp only
  cases he : (prepareStep hC state).1 with
  | done result =>
      have hh := prepareStep_state hC state
      rw [he] at hh
      unfold BinaryResourceChoice.prepare at hh
      split at hh
      · cases hh
      · cases Preparation.done.inj hh
        exact hH
  | ask choice =>
      dsimp only
      rw [BinaryThreeResourceExecution.selectWithCharge_state]
      have hState := prepareStep_choice_state hC state choice he
      exact chooseWithCharge_height hC C s hs hCap (choice.select false)
        (selected_height C s hs hCap choice (hState.symm ▸ hH) false)
termination_by state.state.active.length
decreasing_by
  have h := choice.select_progress false
  rw [prepareStep_choice_state hC state choice he] at h
  exact h

def setupWithCharge (input : BinaryFourParameters.Input) (hC : input.Canonical) : Certified (prepare input).capacity × Charge :=
  let system := prepare input
  let initial := BinaryReflectedResourceWork.initialWithCharge system.capacity system.initial
    (capacity_canonical system (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2
  let later := chooseWithCharge (capacity_canonical system (prepare_canonical input hC)) initial.1
  (later.1,initial.2.add later.2)

theorem setupWithCharge_state (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (setupWithCharge input hC).1 = BinaryResourceFallback.setup input hC := by
  unfold setupWithCharge BinaryResourceFallback.setup
  dsimp only
  rw [BinaryReflectedResourceWork.initialWithCharge_state,chooseWithCharge_state]
  rfl

def bound (s : ℕ) : ℕ := 3000 * (2 + 2 * expressionHeightBudget s 15) ^ 2 + 2 * pairBound 2 (expressionHeightBudget s 15)

theorem setupWithCharge_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) : (setupWithCharge input hC).2.booleanWork ≤ bound s := by
  let system := prepare input
  let hc := capacity_canonical system (prepare_canonical input hC)
  let hr := (prepare_canonical input hC).2.2.2
  let initial := BinaryReflectedResourceWork.initialWithCharge system.capacity system.initial hc hr
  have hCap := fun j => BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH j
  have hResource := fun j => BinaryReflectedResourceWork.initial_resource_height input source hC hR hCase s hs hH j
  have hInitial : StateHeight system.capacity 2 (expressionHeightBudget s 15) initial.1 := by
    rw [BinaryReflectedResourceWork.initialWithCharge_state]
    exact initial_height system.capacity system.initial hc hr _ hResource
  have hScan := BinaryReflectedResourceWork.initialWithCharge_bound system.capacity system.initial hc hr _ (by omega)
    (fun j => (hc j).2.trans (rationalWordWidth_of_height (hCap j)))
    (fun j => (hr j).2.trans (rationalWordWidth_of_height (hResource j)))
  have hLower := chooseWithCharge_bound hc 2 _ (hs.trans (expressionHeightBudget_ge_input s 15)) hCap initial.1 hInitial
  have hScale := Nat.mul_le_mul_right (pairBound 2 (expressionHeightBudget s 15)) hInitial.1
  change initial.2.booleanWork + (chooseWithCharge hc initial.1).2.booleanWork ≤ _
  unfold bound
  change initial.2.booleanWork ≤ 3000 * (1 + 2 * expressionHeightBudget s 15 + 1) ^ 2 at hScan
  simp only [show 1 + 2 * expressionHeightBudget s 15 + 1 = 2 + 2 * expressionHeightBudget s 15 by omega] at hScan
  omega

end Blotto.BinaryThreeResourceFallbackWork
