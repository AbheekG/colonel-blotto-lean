import Blotto.BinaryPRGWordControllerThreeChoiceWork
import Blotto.BinaryPRGWordControllerThreeResource
import Blotto.BinaryPRGWordControllerResourceWork

/-! The actual fixed-three resource source joins Boolean-address pair arithmetic,
selected updates, conservative table copies and the Boolean Store controller.
Unlike the general loop its invariant is the derived rank-indexed rational
height.  No native window/index ledger is transferred by output equality. -/

namespace Blotto.BinaryPRGWordControllerThreeResourceWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryThreeResourcePair BinaryPRGWordControllerThreeChoice BinaryThreeResourceHeight
open BinaryPRGWordControllerThreeChoiceWork
open BinaryPRGWordControllerResourceWork (total total_add)
variable {capacity : FixedArrayTable 3 SignedWord}

def preparationBound (C s : ℕ) : ℕ :=
  BinaryThreeResourceExecution.pairBound C s + 8 * (3 + 4 * resourceHeight C s) + 12

theorem prepareStep_bound (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (state : Certified capacity) (hState : StateHeight capacity C s state) :
    total (prepareStep hC state).2 ≤ preparationBound C s := by
  unfold prepareStep
  split
  · rename_i a b tail he
    have hPair := pair_height hC C s hCap state hState a b tail he
    have hData := BinaryPRGWordControllerPairOutputs.prepareWithWork_bound
      (pairSource hC state a b tail he) (resourceHeight C s)
      (hs.trans (expressionHeightBudget_ge_input s _)) hPair
    have hEnvelope := BinaryPRGWordControllerPairOutputWork.traceBound_le_cubic
      (32 * resourceHeight C s + 31) (by omega)
    have hb : (prepareWithCharge hC state a b tail he).2.booleanWork ≤
        BinaryThreeResourceExecution.pairBound C s := by
      change (BinaryPRGWordControllerPairOutputs.prepareWithWork _).2 ≤ _
      apply hData.trans
      convert hEnvelope using 1 <;>
        simp only [BinaryPRGWordControllerPairOutputs.bound,
          BinaryPRGWordControllerPairOutputWork.traceBound,BinaryThreeResourceExecution.pairBound] <;> ring
    have hc := (pairSource hC state a b tail he).sourcePayloadWork_bound
      (pair_height hC C s hCap state hState a b tail he)
    have hr : (prepareWithCharge hC state a b tail he).2.reads = 4 := rfl
    have hw : (prepareWithCharge hC state a b tail he).2.writes = 0 := rfl
    have hl : (prepareWithCharge hC state a b tail he).2.listControl = 3 := rfl
    have hCopy : (prepareWithCharge hC state a b tail he).2.copyAllowance ≤
        8 * (3 + 4 * resourceHeight C s) + 4 := hc
    rw [total_add]
    change total (prepareWithCharge hC state a b tail he).2 + 1 ≤ _
    unfold total preparationBound
    rw [hr, hw, hl]
    omega
  · unfold total preparationBound
    dsimp only
    omega

theorem selected_endpoint_width (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (choice : Choice capacity hC) (hState : StateHeight capacity C s choice.state) (branch : Bool) :
    width (choice.endpoint branch) ≤ 1 + 2 * resourceHeight C s := by
  have hNext := selected_height C s hs hCap choice.original hState branch
  rw [← choice.select_original] at hNext
  have hw := resource_width C s (choice.select branch) hNext choice.first
  have hd : choice.first ≠ choice.second := by
    intro he
    have hn := choice.state.nodup
    rw [choice.head_pair] at hn
    exact (List.nodup_cons.mp hn).1 (by simp [he])
  unfold Choice.select BinaryThreeResourceState.update at hw
  dsimp only at hw
  rw [FixedArrayTable.read_write, FixedArrayTable.read_write] at hw
  simpa only [hd, ite_false, ite_true] using hw

def selectedBound (C s : ℕ) : ℕ :=
  BinaryThreeResourceExecution.selectBound C s + 25 + 16 * (3 + 4 * resourceHeight C s)

theorem select_bound (hC : ∀ j, CanonicalWord (capacity.read j))
    (C s : ℕ) (hs : 2 ≤ s) (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (choice : Choice capacity hC) (hState : StateHeight capacity C s choice.state) (branch : Bool) :
    total (selectWithCharge choice branch).2 ≤ selectedBound C s := by
  have hBool := BinaryThreeResourceExecution.selectWithCharge_bound C s hs hCap choice.original hState branch
  rw [← selectWithCharge_original] at hBool
  let W := 1 + 2 * resourceHeight C s
  have hResource := fun j => resource_width C s choice.state hState j
  have hChosen := selected_endpoint_width hC C s hs hCap choice hState branch
  have hNext := selected_height C s hs hCap choice.original hState branch
  rw [← choice.select_original] at hNext
  have hOther := resource_width C s (choice.select branch) hNext choice.second
  unfold Choice.select BinaryThreeResourceState.update at hOther
  dsimp only at hOther
  rw [FixedArrayTable.read_write] at hOther
  simp only [ite_true] at hOther
  have hIntermediate : ∀ j, width ((choice.state.state.resource.write choice.first (choice.endpoint branch)).read j) ≤ W := by
    intro j
    rw [FixedArrayTable.read_write]
    split
    · exact hChosen
    · exact hResource j
  have hCopyFirst := BinaryGeneralResourceExecution.writeCopyAllowance_bound choice.state.state.resource
    (choice.endpoint branch) W hResource hChosen
  have hCopySecond := BinaryGeneralResourceExecution.writeCopyAllowance_bound
    (choice.state.state.resource.write choice.first (choice.endpoint branch))
    (BinaryRationalOpcode.apply .sub (BinaryRationalOpcode.apply .add
      (choice.state.state.resource.read choice.first) (choice.state.state.resource.read choice.second)) (choice.endpoint branch))
    W hIntermediate hOther
  have hCaps : ∀ j, width (capacity.read j) ≤ W := fun j =>
    (hC j).2.trans (rationalWordWidth_of_height (capacity_height capacity C s hCap j))
  have hScan := BinaryGeneralResourceExecution.scanWithCharge_bound capacity (choice.select branch).state.resource
    [choice.first, choice.second] W (by dsimp [W]; omega) hCaps (fun j => resource_width C s _ hNext j)
  have hOutput :
      (choice.state.state.resource.write choice.first (choice.endpoint branch)).write choice.second
        (BinaryRationalOpcode.applyWithWork .sub
          (BinaryRationalOpcode.applyWithWork .add (choice.state.state.resource.read choice.first)
            (choice.state.state.resource.read choice.second)).1 (choice.endpoint branch)).1 =
        (choice.select branch).state.resource := by
    simp only [BinaryRationalOpcode.applyWithWork_state]
    rfl
  have hCopy : (selectWithCharge choice branch).2.copyAllowance ≤ 16 * (3 + 4 * resourceHeight C s) := by
    unfold selectWithCharge
    dsimp only
    simp only [BinaryRationalOpcode.applyWithWork_state]
    dsimp [W] at hCopyFirst hCopySecond
    omega
  have hr : (selectWithCharge choice branch).2.reads = 7 := by
    unfold selectWithCharge
    dsimp only
    rw [hOutput]
    simp only [List.length_cons, List.length_nil] at hScan
    omega
  have hw : (selectWithCharge choice branch).2.writes = 2 := rfl
  have hl : (selectWithCharge choice branch).2.listControl = 16 := by
    unfold selectWithCharge
    dsimp only
    rw [hOutput]
    simp only [List.length_cons, List.length_nil] at hScan
    omega
  unfold total selectedBound
  rw [hr, hw, hl]
  omega

def run (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerThreeResource.Result store capacity × ℕ :=
  let prepared := prepareStep hC state
  match hs : prepared.1 with
  | .done result => ((some result, pc), total prepared.2 + 2)
  | .ask choice =>
      let coin := BinaryWordIndexCoinController.sample store choice.probability pc hp
      match coin.1.1 with
      | none => ((none, coin.1.2), total prepared.2 + coin.2 + 2)
      | some branch =>
          let selected := selectWithCharge choice branch
          let later := run store capacity hC selected.1 coin.1.2
            (BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp).2
          (later.1, total prepared.2 + coin.2 + total selected.2 + later.2 + 2)
termination_by state.state.active.length
decreasing_by
  rw [selectWithCharge_state]
  have hw := prepareStep_choice_state hC state choice hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_erasure (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store capacity hC state pc hp).1 = BinaryPRGWordControllerThreeResource.run store capacity hC state pc hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinaryPRGWordControllerThreeResource.run
  rw [← prepareStep_state hC state]
  dsimp only
  cases hs : (prepareStep hC state).1 with
  | done result => rfl
  | ask choice =>
      dsimp only
      simp only [BinaryPRGWordControllerDataCoin.sample_erasure]
      cases hc : (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).1 with
      | none => rfl
      | some branch =>
          dsimp only
          rw [selectWithCharge_state]
          exact run_erasure store capacity hC (choice.select branch)
            (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).2
            (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := prepareStep_choice_state hC state choice hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

def pairBound (C s indexWidth : ℕ) : ℕ :=
  preparationBound C s + selectedBound C s + 12 * (coinWidth C s + 1) +
    BinaryPRGWordControllerThreeResource.bodyBound C s indexWidth + 2

def bound (C s indexWidth active span : ℕ) : ℕ :=
  (active + 1) * pairBound C s indexWidth +
    span * BinaryPRGWordControllerThreeResource.bodyBound C s indexWidth

theorem run_bound (C s : ℕ) (hs : 2 ≤ s) (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (state : Certified capacity)
    (hCap : ∀ j, RationalHeight (value (capacity.read j)) s)
    (hState : StateHeight capacity C s state)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store capacity hC state pc hp).2 ≤ bound C s store.width state.state.active.length
      ((run store capacity hC state pc hp).1.2.value - pc.value) := by
  have hPreparation := prepareStep_bound hC C s hs hCap state hState
  conv_lhs => unfold run
  conv_rhs => arg 5; arg 1; arg 1; unfold run
  dsimp only
  cases hPrepared : (prepareStep hC state).1 with
  | done result => simp only [Nat.sub_self]; unfold bound pairBound; nlinarith
  | ask choice =>
      dsimp only
      have hw := prepareStep_choice_state hC state choice hPrepared
      have hChoice : StateHeight capacity C s choice.state := hw.symm ▸ hState
      have hCoin := BinaryPRGWordControllerThreeResource.coin_bound C s hs store choice hCap hChoice pc hp
      have hPosition := BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp
      cases hcoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 with
      | none => unfold bound pairBound; nlinarith
      | some branch =>
          dsimp only
          have hSelect := select_bound hC C s hs hCap choice hChoice branch
          have hNext := selected_height C s hs hCap choice.original hChoice branch
          rw [← choice.select_original] at hNext
          rw [← selectWithCharge_state choice branch] at hNext
          have ih := run_bound C s hs store capacity hC (selectWithCharge choice branch).1 hCap hNext
            (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2
          have hLength := choice.select_progress branch
          rw [hw, ← selectWithCharge_state choice branch] at hLength
          have hLaterPosition := BinaryPRGWordControllerThreeResource.run_position store capacity hC
            (selectWithCharge choice branch).1
            (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2
          rw [← run_erasure] at hLaterPosition
          have hSpan :
              (run store capacity hC (selectWithCharge choice branch).1
                (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2).1.2.value - pc.value =
              ((BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value - pc.value) +
                ((run store capacity hC (selectWithCharge choice branch).1
                  (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2).1.2.value -
                  (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value) := by omega
          rw [hSpan]
          unfold bound pairBound at ih ⊢
          nlinarith
termination_by state.state.active.length
decreasing_by
  rw [selectWithCharge_state]
  have hw := prepareStep_choice_state hC state choice hPrepared
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

end Blotto.BinaryPRGWordControllerThreeResourceWork
