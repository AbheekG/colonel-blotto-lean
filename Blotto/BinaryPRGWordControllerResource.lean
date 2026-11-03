import Blotto.BinaryPRGWordControllerGeneralChoice
import Blotto.BinaryPRGWordControllerResourceReference
import Blotto.BinaryPRGWordControllerDataCoin
import Blotto.BinaryGeneralResourceRunWork
import Blotto.BinaryPRGResourceWork

/-! The selected general resource path keeps one actual Certified resource
state and one concrete Boolean-word absolute seed counter. Complete coins
resume the exact selected state, with the original shared cap and no decoded
position/window arithmetic. Pair preparation executes the Boolean-address register tree and retains
only lower/upper/probability outputs. The source-derived index/coin/control
ledger is separate from its own pair/tree/table/update arithmetic/copy ledger;
array address/ownership/full bit-machine composition remains further work. -/

namespace Blotto.BinaryPRGWordControllerResource
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryResourcePair BinaryPRGWordControllerGeneralChoice
variable {n : ℕ}

abbrev Result (store : Store) (capacity : FixedArrayTable n SignedWord) :=
  Option (Certified capacity) × FixedBinaryWord store.width

def run (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store capacity :=
  match _hs : BinaryPRGWordControllerGeneralChoice.prepare capacity hC state with
  | .done result => (some result,pc)
  | .ask choice =>
      let coin := BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp
      match coin.1 with
      | none => (none,coin.2)
      | some branch => run store capacity hC (choice.select branch) coin.2
          (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
termination_by state.state.active.length
decreasing_by
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice _hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

def decoded (store : Store) (capacity : FixedArrayTable n SignedWord) (result : Result store capacity) :
    Option (Certified capacity) × ℕ := (result.1,result.2.value)

theorem run_state (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store capacity (run store capacity hC state pc hp) =
      BinaryGeneralResourceRun.runIndexed (hC := hC) store.cap.value
        (BinaryWordIndexCoinController.reader store) (.ready state) pc.value hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinaryGeneralResourceRun.runIndexed
  dsimp only
  rw [← BinaryPRGWordControllerGeneralChoice.prepare_original capacity hC state]
  cases hs : BinaryPRGWordControllerGeneralChoice.prepare capacity hC state with
  | done result => rfl
  | ask choice =>
      dsimp only [Preparation.original]
      rw [BinaryPRGWordControllerResourceReference.pending_compose, ← choice.probability_original]
      have hc := (BinaryPRGWordControllerDataCoin.sample_contract store choice.probability pc hp).1
      have hpc := (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
      have ht := BinaryPRGWordControllerResourceReference.resume_congr store.cap.value
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
      | none => simp only [decoded,BinaryPRGWordControllerResourceReference.resume]
      | some branch =>
          simp only [decoded,BinaryPRGWordControllerResourceReference.resume]
          rw [← choice.select_original]
          exact run_state store capacity hC (choice.select branch)
            (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).2 hpc
termination_by state.state.active.length
decreasing_by
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem run_position (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store capacity hC state pc hp).2.value ∧
      (run store capacity hC state pc hp).2.value ≤ store.cap.value := by
  have h := BinaryGeneralResourceRun.runIndexed_position_bounds (hC := hC) store.cap.value
    (BinaryWordIndexCoinController.reader store) (.ready state) pc.value hp
  have he := congrArg Prod.snd (run_state store capacity hC state pc hp)
  change (run store capacity hC state pc hp).2.value = _ at he
  rw [← he] at h
  exact h

/-- The reached data-only resource path with only its concrete word-counter/
seed-reader/coin/control component annotation. Existing source pair and table
prices are preserved as separate components, not supplied as call oracles. -/
def runWithIndexWork (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store capacity × ℕ :=
  match _hs : BinaryPRGWordControllerGeneralChoice.prepare capacity hC state with
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
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice _hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

theorem runWithIndexWork_erasure (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithIndexWork store capacity hC state pc hp).1 = run store capacity hC state pc hp := by
  conv_lhs => unfold runWithIndexWork
  conv_rhs => unfold run
  dsimp only
  cases hs : BinaryPRGWordControllerGeneralChoice.prepare capacity hC state with
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
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice hs
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl

open BinaryGeneralResourceLattice

def bodyBound (D indexWidth : ℕ) : ℕ :=
  BinaryWordIndexCoinController.allowance (1 + 2 * binaryWordWidth D) indexWidth

def pairBound (D indexWidth : ℕ) : ℕ :=
  12 * (2 + 2 * binaryWordWidth D) + bodyBound D indexWidth + 3

def bound (D indexWidth active span : ℕ) : ℕ :=
  (active + 1) * pairBound D indexWidth + span * bodyBound D indexWidth

theorem coin_bound (D : ℕ) (hD : 0 < D) (store : Store)
    {capacity : FixedArrayTable n SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}
    (choice : Choice capacity hC) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j) ≤ 1) (hs : StateInvariant capacity D choice.state)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordIndexCoinController.sample store choice.probability pc hp).2 ≤
      12 * (2 + 2 * binaryWordWidth D) + bodyBound D store.width *
        ((BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value - pc.value + 1) := by
  have hc := BinaryPRGWordControllerCoinConsumption.sample_bound store choice.probability pc hp
  have hw := prepared_coin_buffer_width choice.original D hD hLattice hUnit hs
  change width choice.original.probability ≤ 1 + 2 * binaryWordWidth D at hw
  rw [← choice.probability_original] at hw
  have hPadding : 12 * (width choice.probability + 1) ≤ 12 * (2 + 2 * binaryWordWidth D) := by omega
  have hBody : BinaryWordIndexCoinController.allowance (width choice.probability) store.width ≤ bodyBound D store.width := by
    unfold bodyBound BinaryWordIndexCoinController.allowance
    omega
  exact hc.trans (Nat.add_le_add hPadding (Nat.mul_le_mul_right _ hBody))

theorem runWithIndexWork_bound (D : ℕ) (hD : 0 < D) (store : Store) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j) ≤ 1) (hs : StateInvariant capacity D state)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithIndexWork store capacity hC state pc hp).2 ≤
      bound D store.width state.state.active.length
        ((runWithIndexWork store capacity hC state pc hp).1.2.value - pc.value) := by
  conv_lhs => unfold runWithIndexWork
  conv_rhs => arg 4; arg 1; arg 1; unfold runWithIndexWork
  dsimp only
  cases hPrepared : BinaryPRGWordControllerGeneralChoice.prepare capacity hC state with
  | done result => simp only [Nat.sub_self]; unfold bound pairBound; nlinarith
  | ask choice =>
      dsimp only
      have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice hPrepared
      have hChoice : StateInvariant capacity D choice.state := hw.symm ▸ hs
      have hCoin := coin_bound D hD store choice hLattice hUnit hChoice pc hp
      have hPosition := BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp
      cases hcoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 with
      | none => unfold bound pairBound; nlinarith
      | some branch =>
          have hSelected := choice_select_invariant choice.original D hLattice hChoice branch
          rw [← choice.select_original] at hSelected
          have ih := runWithIndexWork_bound D hD store capacity hC (choice.select branch) hLattice hUnit hSelected
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
  have hw := BinaryPRGWordControllerGeneralChoice.prepared_state state choice hPrepared
  have hl := choice.select_progress branch
  rw [hw] at hl
  exact hl


theorem reference_reindex (seed : List Bool) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (N M : ℕ) (hNM : N = M) (pos : ℕ) (hp : pos ≤ N) (hq : pos ≤ M) :
    BinaryGeneralResourceRun.runIndexed (hC := hC) N (fun index => seed.getD index.val false) (.ready state) pos hp =
      BinaryGeneralResourceRun.runIndexed (hC := hC) M (fun index => seed.getD index.val false) (.ready state) pos hq := by
  subst M
  rfl

theorem run_prepared_seed (seed : List Bool) (capacity : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (pc : FixedBinaryWord (BinarySeedLookupTree.prepare seed).width)
    (hp : pc.value ≤ (BinarySeedLookupTree.prepare seed).cap.value) :
    decoded (BinarySeedLookupTree.prepare seed) capacity
      (run (BinarySeedLookupTree.prepare seed) capacity hC state pc hp) =
      BinaryGeneralResourceRun.runIndexed (hC := hC) seed.length (fun index => seed.getD index.val false)
        (.ready state) pc.value (by simpa only [cap_value] using hp) := by
  have h := run_state (BinarySeedLookupTree.prepare seed) capacity hC state pc hp
  have hr : BinaryWordIndexCoinController.reader (BinarySeedLookupTree.prepare seed) =
      (fun index => seed.getD index.val false) := by
    funext index
    exact BinaryWordIndexCoinController.reader_prepare seed index
  rw [hr] at h
  exact h.trans (reference_reindex seed capacity hC state _ _ (cap_value seed) pc.value hp
    (by simpa only [cap_value] using hp))

def initialRun (store : Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) : Result store capacity :=
  run store capacity hC (BinaryResourcePair.initial capacity resource hC hR)
    (BinaryWordIndexCoinController.zeroIndex store)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)

theorem initialRun_state (store : Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    decoded store capacity (initialRun store capacity resource hC hR) =
      BinaryGeneralResourceRun.initialRun capacity resource hC hR store.cap.value
        (BinaryWordIndexCoinController.reader store) := by
  unfold initialRun BinaryGeneralResourceRun.initialRun BinaryGeneralResourceRun.run
  have h := run_state store capacity hC (BinaryResourcePair.initial capacity resource hC hR)
    (BinaryWordIndexCoinController.zeroIndex store)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  simpa only [BinaryWordIndexCoinController.zeroIndex_value] using h

def initialRunWithIndexWork (store : Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) : Result store capacity × ℕ :=
  let result := runWithIndexWork store capacity hC (BinaryResourcePair.initial capacity resource hC hR)
    (BinaryWordIndexCoinController.zeroIndex store)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  (result.1,2 * store.width + 1 + result.2)

theorem initialRunWithIndexWork_erasure (store : Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    (initialRunWithIndexWork store capacity resource hC hR).1 = initialRun store capacity resource hC hR := by
  unfold initialRunWithIndexWork initialRun
  exact runWithIndexWork_erasure store capacity hC _ _ _

open BinaryPRGResourceWork

def requestRun (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    Result store (resourceInput request rich).length :=
  initialRun store (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2

theorem requestRun_state (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    decoded store (resourceInput request rich).length (requestRun store request rich) =
      (resourceWork request rich store.cap.value (BinaryWordIndexCoinController.reader store)).1 := by
  have h := initialRun_state store (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2
  exact h.trans (resourceWork_state request rich store.cap.value (BinaryWordIndexCoinController.reader store)).symm

def requestRunWithIndexWork (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    Result store (resourceInput request rich).length × ℕ :=
  initialRunWithIndexWork store (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2

theorem requestRunWithIndexWork_erasure (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (requestRunWithIndexWork store request rich).1 = requestRun store request rich :=
  initialRunWithIndexWork_erasure _ _ _ _ _

def requestBound (n sourceWidth indexWidth N : ℕ) : ℕ :=
  2 * indexWidth + 1 + (n + 1) *
    (12 * (4 + 2 * sourceWidth) + BinaryWordIndexCoinController.allowance (3 + 2 * sourceWidth) indexWidth + 3) +
      N * BinaryWordIndexCoinController.allowance (3 + 2 * sourceWidth) indexWidth

theorem requestRunWithIndexWork_bound (store : Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (requestRunWithIndexWork store request rich).2 ≤
      requestBound n request.source.originalInputWordWidth store.width store.cap.value := by
  obtain ⟨hLengthLattice,hResourceLattice,hCapacityBox,hResourceBox⟩ := resource_lattice_boxes request rich
  have hInvariant := BinaryGeneralResourceLattice.initial_invariant (resourceInput request rich).length
    (resourceInput request rich).resource (resource_canonical request rich).2.1 (resource_canonical request rich).2.2
    request.source.normalizedInput.latticeDenominator hResourceLattice hResourceBox
  have hRun := runWithIndexWork_bound request.source.normalizedInput.latticeDenominator
    request.source.normalizedInput.latticeDenominator_pos store (resourceInput request rich).length
    (resource_canonical request rich).2.1 _ hLengthLattice (fun j => (hCapacityBox j).2) hInvariant
    (BinaryWordIndexCoinController.zeroIndex store)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  have hActive := BinaryGeneralResourceRun.active_length_le
    (BinaryResourcePair.initial (resourceInput request rich).length (resourceInput request rich).resource
      (resource_canonical request rich).2.1 (resource_canonical request rich).2.2)
  have hPosition := (run_position store (resourceInput request rich).length (resource_canonical request rich).2.1
    (BinaryResourcePair.initial (resourceInput request rich).length (resourceInput request rich).resource
      (resource_canonical request rich).2.1 (resource_canonical request rich).2.2)
    (BinaryWordIndexCoinController.zeroIndex store)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)).2
  rw [← runWithIndexWork_erasure] at hPosition
  have hWidth : binaryWordWidth request.source.normalizedInput.latticeDenominator ≤
      request.source.originalInputWordWidth + 1 := by
    have hd := request.source.normalized_lattice_wordWidth_original
    omega
  unfold requestRunWithIndexWork initialRunWithIndexWork requestBound
  dsimp only
  rw [Nat.add_assoc (2 * store.width + 1)]
  apply Nat.add_le_add_left
  unfold bound pairBound bodyBound at hRun
  simp only [BinaryWordIndexCoinController.zeroIndex_value,Nat.sub_zero] at hRun
  apply hRun.trans
  have hBody : BinaryWordIndexCoinController.allowance
      (1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator) store.width ≤
      BinaryWordIndexCoinController.allowance (3 + 2 * request.source.originalInputWordWidth) store.width := by
    unfold BinaryWordIndexCoinController.allowance
    omega
  have hPair : 12 * (2 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator) +
      BinaryWordIndexCoinController.allowance
        (1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator) store.width + 3 ≤
      12 * (4 + 2 * request.source.originalInputWordWidth) +
        BinaryWordIndexCoinController.allowance (3 + 2 * request.source.originalInputWordWidth) store.width + 3 := by omega
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.add_le_add_right hActive 1) hPair)
    (Nat.mul_le_mul hPosition hBody)


end Blotto.BinaryPRGWordControllerResource
