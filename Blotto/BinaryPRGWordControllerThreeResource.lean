import Blotto.BinaryPRGWordControllerThreeChoice
import Blotto.BinaryPRGWordControllerThreeResourceReference
import Blotto.BinaryPRGWordControllerDataCoin
import Blotto.BinaryReflectedResourceWork

/-! The reflected three-resource controller keeps an absolute Boolean seed
counter and one original Certified state. Data-only complete coins share the
whole Store/cap. Exact old local-window/absolute-position semantics are derived
by proof, without decoding or assembling a window in the executable path.
Pair preparation executes the Boolean-address register tree and retains
only its three output words. Own pair/tree and native table/update/copy
prices remain separate components. -/

namespace Blotto.BinaryPRGWordControllerThreeResource
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryThreeResourcePair BinaryPRGWordControllerThreeChoice

abbrev Result (store : Store) (capacity : FixedArrayTable 3 SignedWord) :=
  Option (Certified capacity) × FixedBinaryWord store.width

def run (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store capacity :=
  match _hs : BinaryPRGWordControllerThreeChoice.prepare capacity hC state with
  | .done result => (some result,pc)
  | .ask choice =>
      let coin := BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp
      match coin.1 with
      | none => (none,coin.2)
      | some branch => run store capacity hC (choice.select branch) coin.2
          (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := BinaryPRGWordControllerThreeChoice.prepared_state state choice _hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

def decoded (store : Store) (capacity : FixedArrayTable 3 SignedWord) (result : Result store capacity) :
    Option (Certified capacity) × ℕ := (result.1,result.2.value)

theorem run_state (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store capacity (run store capacity hC state pc hp) =
      BinarySharedResourceRun.runIndexed (hC := hC) store.cap.value
        (BinaryWordIndexCoinController.reader store) (.ready state) pc.value hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinarySharedResourceRun.runIndexed
  dsimp only
  rw [← BinaryPRGWordControllerThreeChoice.prepare_original capacity hC state]
  cases hs : BinaryPRGWordControllerThreeChoice.prepare capacity hC state with
  | done result => rfl
  | ask choice =>
      dsimp only [Preparation.original]
      rw [BinaryPRGWordControllerThreeResourceReference.pending_compose, ← choice.probability_original]
      have hc := (BinaryPRGWordControllerDataCoin.sample_contract store choice.probability pc hp).1
      have hpc := (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
      have ht := BinaryPRGWordControllerThreeResourceReference.resume_congr store.cap.value
        (BinaryWordIndexCoinController.reader store) choice.original
        ((BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).1,
          (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).2.value)
        (BinaryStoredCoinIndexed.sample choice.probability store.cap.value
          (BinaryWordIndexCoinController.reader store) pc.value hp) hpc
        (BinaryPRGWordControllerCategoricalReference.coin_position store.cap.value
          (BinaryWordIndexCoinController.reader store)
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).1
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).2 pc.value hp).2 hc
      apply Eq.trans ?_ ht
      cases hcoin : (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).1 with
      | none => simp only [decoded,BinaryPRGWordControllerThreeResourceReference.resume]
      | some branch =>
          simp only [decoded,BinaryPRGWordControllerThreeResourceReference.resume]
          rw [← choice.select_original]
          exact run_state store capacity hC (choice.select branch)
            (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).2 hpc
termination_by state.state.active.length
decreasing_by
  have hw := BinaryPRGWordControllerThreeChoice.prepared_state state choice hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_position (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store capacity hC state pc hp).2.value ∧
      (run store capacity hC state pc hp).2.value ≤ store.cap.value := by
  have hRef := BinarySharedResourceRun.runIndexed_refines (hC := hC) store.cap.value
    (BinaryWordIndexCoinController.reader store) (.ready state) pc.value hp
  have h := (rationalResourceMachine (fun j => value (capacity.read j))).runCursorIndexed_position_bounds
    store.cap.value (BinaryWordIndexCoinController.reader store)
    (BinarySharedResourceRun.Cursor.ready (hC := hC) state).reference pc.value hp
  rw [← hRef] at h
  change pc.value ≤ (BinarySharedResourceRun.runIndexed (hC := hC) store.cap.value
    (BinaryWordIndexCoinController.reader store) (.ready state) pc.value hp).2 ∧
      (BinarySharedResourceRun.runIndexed (hC := hC) store.cap.value
        (BinaryWordIndexCoinController.reader store) (.ready state) pc.value hp).2 ≤ store.cap.value at h
  have he := congrArg Prod.snd (run_state store capacity hC state pc hp)
  change (run store capacity hC state pc hp).2.value = _ at he
  rw [← he] at h
  exact h

/-- The reached data-only resource path with only its concrete word-counter/
seed-reader/coin/control component annotation. Existing source pair and table
prices are preserved as separate components, not supplied as call oracles. -/
def runWithIndexWork (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store capacity × ℕ :=
  match _hs : BinaryPRGWordControllerThreeChoice.prepare capacity hC state with
  | .done result => ((some result,pc),3)
  | .ask choice =>
      let coin := BinaryWordIndexCoinController.sample store choice.probability pc hp
      match coin.1.1 with
      | none => ((none,coin.1.2),coin.2 + 3)
      | some branch =>
          let later := runWithIndexWork store capacity hC (choice.select branch) coin.1.2
            (BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp).2
          (later.1,coin.2 + later.2 + 3)
termination_by state.state.active.length
decreasing_by
  have hw := BinaryPRGWordControllerThreeChoice.prepared_state state choice _hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem runWithIndexWork_erasure (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithIndexWork store capacity hC state pc hp).1 = run store capacity hC state pc hp := by
  conv_lhs => unfold runWithIndexWork
  conv_rhs => unfold run
  dsimp only
  cases hs : BinaryPRGWordControllerThreeChoice.prepare capacity hC state with
  | done result => rfl
  | ask choice =>
      dsimp only
      simp only [BinaryPRGWordControllerDataCoin.sample_erasure]
      cases hc : (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).1 with
      | none => rfl
      | some branch =>
          exact runWithIndexWork_erasure store capacity hC (choice.select branch)
            (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).2
            (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := BinaryPRGWordControllerThreeChoice.prepared_state state choice hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl


open BinaryThreeResourceHeight

def bodyBound (C s indexWidth : ℕ) : ℕ :=
  BinaryWordIndexCoinController.allowance (coinWidth C s) indexWidth

def pairBound (C s indexWidth : ℕ) : ℕ :=
  12 * (coinWidth C s + 1) + bodyBound C s indexWidth + 3

def bound (C s indexWidth active span : ℕ) : ℕ :=
  (active + 1) * pairBound C s indexWidth + span * bodyBound C s indexWidth

theorem coin_bound (C s : ℕ) (hs : 2 ≤ s) (store : Store)
    {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (hCap : ∀ j,RationalHeight (value (capacity.read j)) s)
    (hState : StateHeight capacity C s choice.state)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordIndexCoinController.sample store choice.probability pc hp).2 ≤
      12 * (coinWidth C s + 1) + bodyBound C s store.width *
        ((BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value - pc.value + 1) := by
  have hc := BinaryPRGWordControllerCoinConsumption.sample_bound store choice.probability pc hp
  have hw := probability_width C s hs hCap choice.original hState
  rw [← choice.probability_original] at hw
  have hPadding : 12 * (width choice.probability + 1) ≤ 12 * (coinWidth C s + 1) := by omega
  have hBody : BinaryWordIndexCoinController.allowance (width choice.probability) store.width ≤ bodyBound C s store.width := by
    unfold bodyBound BinaryWordIndexCoinController.allowance
    omega
  exact hc.trans (Nat.add_le_add hPadding (Nat.mul_le_mul_right _ hBody))

theorem runWithIndexWork_bound (C s : ℕ) (hs : 2 ≤ s) (store : Store) (capacity : FixedArrayTable 3 SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (hCap : ∀ j,RationalHeight (value (capacity.read j)) s) (hState : StateHeight capacity C s state)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithIndexWork store capacity hC state pc hp).2 ≤
      bound C s store.width state.state.active.length
        ((runWithIndexWork store capacity hC state pc hp).1.2.value - pc.value) := by
  conv_lhs => unfold runWithIndexWork
  conv_rhs => arg 5; arg 1; arg 1; unfold runWithIndexWork
  dsimp only
  cases hPrepared : BinaryPRGWordControllerThreeChoice.prepare capacity hC state with
  | done result => simp only [Nat.sub_self]; unfold bound pairBound; nlinarith
  | ask choice =>
      dsimp only
      have hw := BinaryPRGWordControllerThreeChoice.prepared_state state choice hPrepared
      have hChoice : StateHeight capacity C s choice.state := hw.symm ▸ hState
      have hCoin := coin_bound C s hs store choice hCap hChoice pc hp
      have hPosition := BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp
      cases hcoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 with
      | none => unfold bound pairBound; nlinarith
      | some branch =>
          have hSelected := selected_height C s hs hCap choice.original hChoice branch
          rw [← choice.select_original] at hSelected
          have ih := runWithIndexWork_bound C s hs store capacity hC (choice.select branch) hCap hSelected
            (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2
          have hLength := choice.select_progress branch
          rw [hw] at hLength
          have hLaterPosition := run_position store capacity hC (choice.select branch)
            (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2
          rw [← runWithIndexWork_erasure] at hLaterPosition
          have hSpan :
              (runWithIndexWork store capacity hC (choice.select branch)
                (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2).1.2.value - pc.value =
              ((BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value - pc.value) +
                ((runWithIndexWork store capacity hC (choice.select branch)
                  (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2).1.2.value -
                  (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value) := by omega
          rw [hSpan]
          unfold bound pairBound at ih ⊢
          nlinarith
termination_by state.state.active.length
decreasing_by
  have hw := BinaryPRGWordControllerThreeChoice.prepared_state state choice hPrepared
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

open BinaryReflectedFourSetup

def setupIndexed (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Result store (prepare input).capacity :=
  let prepared := prepare input
  run store prepared.capacity (capacity_canonical prepared (prepare_canonical input hC))
    (BinaryThreeResourcePair.initial prepared.capacity prepared.initial
      (capacity_canonical prepared (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2) pc hp

theorem setupIndexed_state (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (prepare input).capacity (setupIndexed store input hC pc hp) =
      WordStateMachine.offsetConsumed pc.value (BinarySharedResourceRun.setupRun input hC
        (store.cap.value - pc.value)
        (WordStateMachine.inputWindow (BinaryWordIndexCoinController.reader store) pc.value
          (store.cap.value - pc.value) (by omega))) := by
  unfold setupIndexed BinarySharedResourceRun.setupRun BinarySharedResourceRun.run
  rw [run_state,BinaryPRGWordControllerThreeResourceReference.runIndexed_window]
  rfl

theorem setupIndexed_position (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (setupIndexed store input hC pc hp).2.value ∧
      (setupIndexed store input hC pc hp).2.value ≤ store.cap.value :=
  run_position store _ _ _ pc hp

def setupIndexedWithWork (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Result store (prepare input).capacity × ℕ :=
  let prepared := prepare input
  runWithIndexWork store prepared.capacity (capacity_canonical prepared (prepare_canonical input hC))
    (BinaryThreeResourcePair.initial prepared.capacity prepared.initial
      (capacity_canonical prepared (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2) pc hp

theorem setupIndexedWithWork_erasure (store : Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (setupIndexedWithWork store input hC pc hp).1 = setupIndexed store input hC pc hp :=
  runWithIndexWork_erasure store _ _ _ pc hp

theorem setupIndexedWithWork_bound (store : Store) (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (setupIndexedWithWork store input hC pc hp).2 ≤
      bound 2 (expressionHeightBudget s 15) store.width 3
        ((setupIndexedWithWork store input hC pc hp).1.2.value - pc.value) := by
  have hCap := BinaryReflectedResourceWork.capacity_height input source hC hR hCase s hs hH
  have hInit := BinaryReflectedResourceWork.initial_resource_height input source hC hR hCase s hs hH
  have hState := initial_height (prepare input).capacity (prepare input).initial
    (capacity_canonical _ (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2
    (expressionHeightBudget s 15) hInit
  have hRun := runWithIndexWork_bound 2 (expressionHeightBudget s 15)
    (hs.trans (expressionHeightBudget_ge_input _ _)) store (prepare input).capacity
    (capacity_canonical _ (prepare_canonical input hC)) _ hCap hState pc hp
  have hLen : (BinaryThreeResourcePair.initial (prepare input).capacity (prepare input).initial
      (capacity_canonical _ (prepare_canonical input hC)) (prepare_canonical input hC).2.2.2).state.active.length ≤ 3 :=
    (List.length_filter_le _ _).trans_eq (by simp)
  apply hRun.trans
  unfold bound
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right hLen 1)) _

end Blotto.BinaryPRGWordControllerThreeResource
