import Blotto.BinaryPRGWordControllerGeneralChoiceWork
import Blotto.BinaryPRGWordControllerResource
import Blotto.BinaryPRGWordControllerBooleanResourceSourceWork

/-! Actual reached resource preparation and selected table update are joined
to the concrete Boolean seed lookup/increment controller.  Pair preparation follows the Boolean-address register backend and its
own derived quadratic price. The complete initial/request entry builds one cached Boolean capacity/resource tree pair,
uses Boolean active identifiers and performs actual selected tree updates. Arbitrary
native-state run remains available as the old specification path.
Logical table accesses and conservative copy cells are retained explicitly;
this is not a transfer of an old runner's charge by output equality. -/

namespace Blotto.BinaryPRGWordControllerResourceWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryResourcePair BinaryPRGWordControllerGeneralChoice
open BinaryGeneralResourceExecution (Charge initialWithCharge initialWithCharge_state initialWithCharge_lattice_bound)
open BinaryPRGWordControllerGeneralChoiceWork
open BinaryGeneralResourceLattice
variable {n : ℕ}

def total (charge : Charge) : ℕ :=
  charge.booleanWork + charge.reads + charge.writes + charge.listControl + charge.copyAllowance

theorem total_add (first second : Charge) : total (first.add second) = total first + total second := by
  cases first
  cases second
  unfold total Charge.add
  dsimp only
  omega

def preparationBound (D : ℕ) : ℕ :=
  7 * (12000 * (4 + 2 * binaryWordWidth D)^3 + 28 * (7 + 4 * binaryWordWidth D) + 4) +
    8 * (3 + 4 * binaryWordWidth D) + 12

set_option maxHeartbeats 1000000 in
theorem prepareStep_bound (D : ℕ) (hD : 0 < D) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (state : Certified capacity)
    (hLattice : ∀ j, OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j, 0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hs : StateInvariant capacity D state) :
    total (prepareStep hC state).2 ≤ preparationBound D := by
  unfold prepareStep
  split
  · rename_i first second tail he
    let source := pairSource hC state first second tail he
    let W := 3 + 2 * binaryWordWidth D
    have hTrace := pair_trace_wordBounds hC state first second tail he D hD hLattice
      (fun j => (hBox j).2) hs
    have hData := BinaryPRGWordControllerPairOutputWork.prepare_trace_bound source W hTrace
    have hEnvelope := BinaryPRGWordControllerPairOutputWork.traceBound_le_cubic W (by dsimp [W]; omega)
    have hBool : (prepareWithCharge hC state first second tail he).2.booleanWork ≤
        7 * (12000 * (4 + 2 * binaryWordWidth D)^3 + 28 * (7 + 4 * binaryWordWidth D) + 4) := by
      change (BinaryPRGWordControllerPairOutputs.prepareWithWork source).2 ≤ _
      apply hData.trans
      convert hEnvelope using 1 <;> dsimp [W] <;> ring
    have hCopy := BinaryGeneralResourceExecution.prepareWithCharge_copy_bound hC state first second tail he
      D hD hLattice hBox hs
    change (prepareWithCharge hC state first second tail he).2.copyAllowance ≤
      8 * (3 + 4 * binaryWordWidth D) + 4 at hCopy
    have hr : (prepareWithCharge hC state first second tail he).2.reads = 4 := rfl
    have hw : (prepareWithCharge hC state first second tail he).2.writes = 0 := rfl
    have hl : (prepareWithCharge hC state first second tail he).2.listControl = 3 := rfl
    rw [total_add]
    change total (prepareWithCharge hC state first second tail he).2 + 1 ≤ _
    unfold total preparationBound
    rw [hr, hw, hl]
    omega
  · unfold total preparationBound
    dsimp only
    omega

def selectedBound (n D : ℕ) : ℕ :=
  24000 * (4 + 2 * binaryWordWidth D)^3 + 2000 * (2 + 2 * binaryWordWidth D)^2 +
    25 + 4 * (n + 1) * (3 + 4 * binaryWordWidth D)

theorem select_bound (D : ℕ) (hD : 0 < D) {capacity : FixedArrayTable n SignedWord}
    {hC : ∀ j, CanonicalWord (capacity.read j)} (choice : Choice capacity hC)
    (hLattice : ∀ j, OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j, 0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hs : StateInvariant capacity D choice.state) (branch : Bool) :
    total (selectWithCharge choice branch).2 ≤ selectedBound n D := by
  rw [selectWithCharge_original]
  obtain ⟨hb, hr, hw, hl, hc⟩ := BinaryGeneralResourceExecution.selectWithCharge_lattice_bound choice.original D hD hLattice hBox hs branch
  unfold total selectedBound
  omega

def run (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerResource.Result store capacity × ℕ :=
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
  have hPrepared : BinaryPRGWordControllerGeneralChoice.prepare capacity hC state = .ask choice :=
    (prepareStep_state hC state).symm.trans hs
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice hPrepared
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_erasure (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store capacity hC state pc hp).1 = BinaryPRGWordControllerResource.run store capacity hC state pc hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinaryPRGWordControllerResource.run
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
  have hPrepared : BinaryPRGWordControllerGeneralChoice.prepare capacity hC state = .ask choice :=
    (prepareStep_state hC state).symm.trans hs
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice hPrepared
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

def pairBound (n D indexWidth : ℕ) : ℕ :=
  preparationBound D + selectedBound n D + 12 * (2 + 2 * binaryWordWidth D) +
    BinaryPRGWordControllerResource.bodyBound D indexWidth + 2

def bound (n D indexWidth active span : ℕ) : ℕ :=
  (active + 1) * pairBound n D indexWidth + span * BinaryPRGWordControllerResource.bodyBound D indexWidth

theorem run_bound (D : ℕ) (hD : 0 < D) (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (state : Certified capacity)
    (hLattice : ∀ j, OnRationalLattice D (value (capacity.read j)))
    (hBox : ∀ j, 0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hs : StateInvariant capacity D state)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store capacity hC state pc hp).2 ≤ bound n D store.width state.state.active.length
      ((run store capacity hC state pc hp).1.2.value - pc.value) := by
  have hPreparation := prepareStep_bound D hD capacity hC state hLattice hBox hs
  conv_lhs => unfold run
  conv_rhs => arg 5; arg 1; arg 1; unfold run
  dsimp only
  cases hPrepared : (prepareStep hC state).1 with
  | done result =>
      simp only [Nat.sub_self]
      unfold bound pairBound
      nlinarith
  | ask choice =>
      dsimp only
      have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice
        ((prepareStep_state hC state).symm.trans hPrepared)
      have hChoice : StateInvariant capacity D choice.state := hw.symm ▸ hs
      have hCoin := BinaryPRGWordControllerResource.coin_bound D hD store choice hLattice
        (fun j => (hBox j).2) hChoice pc hp
      have hPosition := BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp
      cases hcoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 with
      | none => unfold bound pairBound; nlinarith
      | some branch =>
          dsimp only
          have hSelect := select_bound D hD choice hLattice hBox hChoice branch
          have hNext := choice_select_invariant choice.original D hLattice hChoice branch
          rw [← choice.select_original] at hNext
          rw [← selectWithCharge_state choice branch] at hNext
          have ih := run_bound D hD store capacity hC (selectWithCharge choice branch).1 hLattice hBox hNext
            (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2
          have hLength := choice.select_progress branch
          rw [hw, ← selectWithCharge_state choice branch] at hLength
          have hLaterPosition := BinaryPRGWordControllerResource.run_position store capacity hC
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
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice
    ((prepareStep_state hC state).symm.trans hPrepared)
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

def initialRun (store : Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) :
    BinaryPRGWordControllerResource.Result store capacity × ℕ :=
  BinaryPRGWordControllerBooleanResourceSourceWork.initialRun store capacity resource hC hR

theorem initialRun_erasure (store : Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j)) :
    (initialRun store capacity resource hC hR).1 = BinaryPRGWordControllerResource.initialRun store capacity resource hC hR := by
  exact BinaryPRGWordControllerBooleanResourceSourceWork.initialRun_erasure store capacity resource hC hR

def initialBound (n D indexWidth N : ℕ) : ℕ :=
  n * (1000 * (2 + 2 * binaryWordWidth D)^2) + 8 * n + 2 +
    2 * indexWidth + 1 + bound n D indexWidth n N +
      BinaryPRGWordControllerBooleanResourceSourceWork.initialBound n D (n + 1) indexWidth N

theorem initialRun_bound (D : ℕ) (hD : 0 < D) (store : Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j, CanonicalWord (capacity.read j)) (hR : ∀ j, CanonicalWord (resource.read j))
    (hLattice : ∀ j, OnRationalLattice D (value (capacity.read j)))
    (hResource : ∀ j, OnRationalLattice D (value (resource.read j)))
    (hBox : ∀ j, 0 ≤ value (capacity.read j) ∧ value (capacity.read j) ≤ 1)
    (hResourceBox : ∀ j, 0 ≤ value (resource.read j) ∧ value (resource.read j) ≤ value (capacity.read j)) :
    (initialRun store capacity resource hC hR).2 ≤ initialBound n D store.width store.cap.value := by
  have h := BinaryPRGWordControllerBooleanResourceSourceWork.initialRun_dimension_bound D hD store capacity resource
    hC hR hLattice hResource hBox hResourceBox
  exact h.trans (Nat.le_add_left _ _)

def requestRun (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    BinaryPRGWordControllerResource.Result store (BinaryPRGResourceWork.resourceInput request rich).length × ℕ :=
  initialRun store (BinaryPRGResourceWork.resourceInput request rich).length
    (BinaryPRGResourceWork.resourceInput request rich).resource
    (BinaryPRGResourceWork.resource_canonical request rich).2.1
    (BinaryPRGResourceWork.resource_canonical request rich).2.2

theorem requestRun_erasure (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (requestRun store request rich).1 = BinaryPRGWordControllerResource.requestRun store request rich :=
  initialRun_erasure _ _ _ _ _

theorem requestRun_bound (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (requestRun store request rich).2 ≤ initialBound n request.source.normalizedInput.latticeDenominator store.width store.cap.value := by
  obtain ⟨hL,hR,hBox,hResourceBox⟩ := BinaryPRGResourceWork.resource_lattice_boxes request rich
  exact initialRun_bound _ request.source.normalizedInput.latticeDenominator_pos _ _ _ _ _ hL hR hBox hResourceBox

end Blotto.BinaryPRGWordControllerResourceWork
