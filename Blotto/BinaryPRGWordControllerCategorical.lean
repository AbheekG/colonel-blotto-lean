import Blotto.BinaryPRGWordControllerCoinConsumption
import Blotto.BinaryPRGWordControllerPreparation
import Blotto.BinaryPRGWordControllerCategoricalReference
import Blotto.BinaryStoredSegmentChoiceWork

/-! A complete categorical linked-list controller uses concrete quadratic
Boolean preparation and a single shared Boolean-word seed counter. Reached
coins keep the exact same cap and original remaining suffix; no numeric seed
position, suffix window or per-coin cap is assembled. Exact results and absolute
positions refine the retained native selector. The derived aggregate charges
actual consumed bits only once across all reached coins. -/

namespace Blotto.BinaryPRGWordControllerCategorical
open BinarySeedLookupTree BinaryRationalNormalization BinaryCategoricalPreparation BinaryCategoricalRun

abbrev Result (α : Type*) (store : Store) := (Option α × FixedBinaryWord store.width) × ℕ

def run {α : Type*} (store : Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result α store :=
  let prepared := BinaryPRGWordControllerPreparation.prepareWithWork fallback weights
  match hs : prepared.1 with
  | .done selected => ((some selected,pc),prepared.2 + 2)
  | .ask choice =>
      let coin := BinaryWordIndexCoinController.sample store choice.probability pc hp
      match coin.1.1 with
      | none => ((none,coin.1.2),prepared.2 + coin.2 + 2)
      | some true => ((some choice.head.1,coin.1.2),prepared.2 + coin.2 + 2)
      | some false =>
          let later := run store fallback choice.rest coin.1.2
            (BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp).2
          (later.1,prepared.2 + coin.2 + later.2 + 2)
termination_by weights.items.length
decreasing_by
  have hw := BinaryPRGWordControllerPreparation.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

def decoded {α : Type*} (store : Store) (result : Result α store) : Option α × ℕ :=
  (result.1.1,result.1.2.value)

theorem run_state {α : Type*} (store : Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (run store fallback weights pc hp) =
      BinaryCategoricalRun.runIndexed fallback store.cap.value (BinaryWordIndexCoinController.reader store)
        (.remaining weights) pc.value hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinaryCategoricalRun.runIndexed
  rw [← BinaryPRGWordControllerPreparation.prepareWithWork_state fallback weights]
  dsimp only
  cases hs : (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 with
  | done selected => rfl
  | ask choice =>
      dsimp only
      rw [BinaryPRGWordControllerCategoricalReference.pending_compose]
      have hc := BinaryWordIndexCoinController.sample_state store choice.probability pc hp
      have hpc := (BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp).2
      have ht := BinaryPRGWordControllerCategoricalReference.resume_congr fallback store.cap.value
        (BinaryWordIndexCoinController.reader store) choice
        (BinaryWordIndexCoinController.decoded store
          (BinaryWordIndexCoinController.sample store choice.probability pc hp))
        (BinaryStoredCoinIndexed.sample choice.probability store.cap.value
          (BinaryWordIndexCoinController.reader store) pc.value hp) hpc
        (BinaryPRGWordControllerCategoricalReference.coin_position store.cap.value
          (BinaryWordIndexCoinController.reader store)
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).1
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).2 pc.value hp).2 hc
      apply Eq.trans ?_ ht
      cases hcoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 with
      | none => simp only [hcoin,decoded,BinaryWordIndexCoinController.decoded,BinaryPRGWordControllerCategoricalReference.resume]
      | some branch =>
          cases branch
          · simp only [hcoin,decoded,BinaryWordIndexCoinController.decoded,BinaryPRGWordControllerCategoricalReference.resume]
            exact run_state store fallback choice.rest
              (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hpc
          · simp only [hcoin,decoded,BinaryWordIndexCoinController.decoded,BinaryPRGWordControllerCategoricalReference.resume]
termination_by weights.items.length
decreasing_by
  have hw := BinaryPRGWordControllerPreparation.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem run_position_bounds {α : Type*} (store : Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store fallback weights pc hp).1.2.value ∧
      (run store fallback weights pc hp).1.2.value ≤ store.cap.value := by
  conv_lhs => unfold run
  conv_rhs => unfold run
  dsimp only
  cases hs : (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 with
  | done selected => exact ⟨le_rfl,hp⟩
  | ask choice =>
      dsimp only
      have hCoin := BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp
      cases hcoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 with
      | none => simpa only [hcoin] using hCoin
      | some branch =>
          cases branch
          · simp only
            have ih := run_position_bounds store fallback choice.rest
              (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hCoin.2
            exact ⟨hCoin.1.trans ih.1,ih.2⟩
          · simpa only [hcoin] using hCoin
termination_by weights.items.length
decreasing_by
  have hw := BinaryPRGWordControllerPreparation.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

open BinaryCategoricalUnitLattice

def bodyBound (D indexWidth : ℕ) : ℕ :=
  BinaryWordIndexCoinController.allowance (5 + 8 * binaryWordWidth D) indexWidth

def choiceBound (D length indexWidth : ℕ) : ℕ :=
  BinaryPRGWordControllerPreparation.preparationBound D length +
    12 * (6 + 8 * binaryWordWidth D) + bodyBound D indexWidth + 2

def bound (D length indexWidth span : ℕ) : ℕ :=
  (length + 1) * choiceBound D length indexWidth + span * bodyBound D indexWidth

theorem choiceBound_mono (D indexWidth : ℕ) {first second : ℕ} (h : first ≤ second) :
    choiceBound D first indexWidth ≤ choiceBound D second indexWidth := by
  unfold choiceBound BinaryPRGWordControllerPreparation.preparationBound
  have hm := Nat.mul_le_mul_right (11000 * (2 + 2 * binaryWordWidth D)^2 + 2)
    (Nat.add_le_add_right h 1)
  omega

theorem coin_bound {α : Type*} (D : ℕ) (hD : 0 < D) (store : Store) (choice : Choice α)
    (hUnit : UnitLattice D choice.weights) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordIndexCoinController.sample store choice.probability pc hp).2 ≤
      12 * (6 + 8 * binaryWordWidth D) + bodyBound D store.width *
        ((BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value - pc.value + 1) := by
  have hc := BinaryPRGWordControllerCoinConsumption.sample_bound store choice.probability pc hp
  have hw := choice_probability_width D hD choice hUnit
  change width choice.probability ≤ 5 + 8 * binaryWordWidth D at hw
  have hPadding : 12 * (width choice.probability + 1) ≤ 12 * (6 + 8 * binaryWordWidth D) := by omega
  have hBody : BinaryWordIndexCoinController.allowance (width choice.probability) store.width ≤ bodyBound D store.width := by
    unfold bodyBound BinaryWordIndexCoinController.allowance
    omega
  exact hc.trans (Nat.add_le_add hPadding (Nat.mul_le_mul_right _ hBody))

theorem run_bound {α : Type*} (D : ℕ) (hD : 0 < D) (store : Store) (fallback : α) (weights : WeightList α)
    (hUnit : UnitLattice D weights) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store fallback weights pc hp).2 ≤
      bound D weights.items.length store.width ((run store fallback weights pc hp).1.2.value - pc.value) := by
  have hPreparation := BinaryPRGWordControllerPreparation.prepareWithWork_bound D hD fallback weights hUnit
  conv_lhs => unfold run
  conv_rhs => arg 4; arg 1; arg 1; unfold run
  dsimp only
  cases hs : (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 with
  | done selected =>
      simp only [Nat.sub_self]
      unfold bound choiceBound
      nlinarith
  | ask choice =>
      dsimp only
      have hw := BinaryPRGWordControllerPreparation.prepared_choice_weights fallback weights choice hs
      have hChoice : UnitLattice D choice.weights := hw.symm ▸ hUnit
      have hCoin := coin_bound D hD store choice hChoice pc hp
      have hPosition := BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp
      cases hcoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 with
      | none => simp only; unfold bound choiceBound; nlinarith
      | some branch =>
          cases branch
          · simp only
            have hRest := choice_rest_unit D choice hChoice
            have ih := run_bound D hD store fallback choice.rest hRest
              (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2
            have hLength := rest_length choice
            rw [hw] at hLength
            have hMon := choiceBound_mono D store.width (by omega : choice.rest.items.length ≤ weights.items.length)
            have hLaterPosition := run_position_bounds store fallback choice.rest
              (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2 hPosition.2
            have hSpan :
                (run store fallback choice.rest (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2
                  hPosition.2).1.2.value - pc.value =
                ((BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value - pc.value) +
                  ((run store fallback choice.rest (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2
                    hPosition.2).1.2.value -
                    (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2.value) := by omega
            rw [hSpan]
            unfold bound at ih ⊢
            have hi := ih.trans (Nat.add_le_add_right
              (Nat.mul_le_mul_left _ hMon) _)
            unfold choiceBound at *
            nlinarith
          · simp only; unfold bound choiceBound; nlinarith
termination_by weights.items.length
decreasing_by
  have hw := BinaryPRGWordControllerPreparation.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega


/-- Finite control labels for the actual preparation/coin/continuation trace.
The scalar/index/reader blocks are concrete verified Boolean algorithms, not
abstract calls whose behavior or price a caller supplies. -/
inductive Event where
  | prepared
  | returned
  | exhausted
  | selected
  | continued
  deriving DecidableEq

/-- Compositional operational semantics for the complete linked-list selector.
The result contains the exact joined primitive ledger; every constructor ties
its preparation/coin result and cost to the concrete implemented algorithms. -/
inductive Execution {α : Type*} (store : Store) (fallback : α) :
    (weights : WeightList α) → (pc : FixedBinaryWord store.width) →
      (hp : pc.value ≤ store.cap.value) → Result α store → List Event → Prop where
  | returned (weights : WeightList α) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
      (selected : α)
      (hPrepared : (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 = .done selected) :
      Execution store fallback weights pc hp
        ((some selected,pc),(BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).2 + 2)
        [.prepared,.returned]
  | exhausted (weights : WeightList α) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
      (choice : Choice α)
      (hPrepared : (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 = .ask choice)
      (hCoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 = none) :
      Execution store fallback weights pc hp
        ((none,(BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2),
          (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).2 +
            (BinaryWordIndexCoinController.sample store choice.probability pc hp).2 + 2)
        [.prepared,.exhausted]
  | selected (weights : WeightList α) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
      (choice : Choice α)
      (hPrepared : (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 = .ask choice)
      (hCoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 = some true) :
      Execution store fallback weights pc hp
        ((some choice.head.1,(BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2),
          (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).2 +
            (BinaryWordIndexCoinController.sample store choice.probability pc hp).2 + 2)
        [.prepared,.selected]
  | continued (weights : WeightList α) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
      (choice : Choice α)
      (hPrepared : (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 = .ask choice)
      (hCoin : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 = some false)
      (later : Result α store) (trace : List Event)
      (hLater : Execution store fallback choice.rest
        (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2
        (BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp).2 later trace) :
      Execution store fallback weights pc hp
        (later.1,(BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).2 +
          (BinaryWordIndexCoinController.sample store choice.probability pc hp).2 + later.2 + 2)
        (.prepared :: .continued :: trace)

theorem run_has_execution {α : Type*} (store : Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ∃ trace, Execution store fallback weights pc hp (run store fallback weights pc hp) trace := by
  unfold run
  dsimp only
  cases hs : (BinaryPRGWordControllerPreparation.prepareWithWork fallback weights).1 with
  | done selected => exact ⟨_,Execution.returned weights pc hp selected hs⟩
  | ask choice =>
      dsimp only
      cases hc : (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.1 with
      | none => exact ⟨_,Execution.exhausted weights pc hp choice hs hc⟩
      | some branch =>
          cases branch
          · obtain ⟨trace,hTrace⟩ := run_has_execution store fallback choice.rest
              (BinaryWordIndexCoinController.sample store choice.probability pc hp).1.2
              (BinaryWordIndexCoinController.sample_position_bounds store choice.probability pc hp).2
            exact ⟨_,Execution.continued weights pc hp choice hs hc _ trace hTrace⟩
          · exact ⟨_,Execution.selected weights pc hp choice hs hc⟩
termination_by weights.items.length
decreasing_by
  have hw := BinaryPRGWordControllerPreparation.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem execution_eq_run {α : Type*} {store : Store} {fallback : α} {weights : WeightList α}
    {pc : FixedBinaryWord store.width} {hp : pc.value ≤ store.cap.value} {result : Result α store}
    {trace : List Event} (h : Execution store fallback weights pc hp result trace) :
    result = run store fallback weights pc hp := by
  induction h with
  | returned weights pc hp selected hPrepared =>
      conv_rhs => unfold run
      dsimp only
      rw [hPrepared]
  | exhausted weights pc hp choice hPrepared hCoin =>
      conv_rhs => unfold run
      dsimp only
      rw [hPrepared]
      simp only [hCoin]
  | selected weights pc hp choice hPrepared hCoin =>
      conv_rhs => unfold run
      dsimp only
      rw [hPrepared]
      simp only [hCoin]
  | continued weights pc hp choice hPrepared hCoin later trace hLater ih =>
      conv_rhs => unfold run
      dsimp only
      rw [hPrepared]
      simp only [hCoin]
      rw [← ih]

theorem execution_refines {α : Type*} {store : Store} {fallback : α} {weights : WeightList α}
    {pc : FixedBinaryWord store.width} {hp : pc.value ≤ store.cap.value} {result : Result α store}
    {trace : List Event} (h : Execution store fallback weights pc hp result trace) :
    decoded store result = BinaryCategoricalRun.runIndexed fallback store.cap.value
      (BinaryWordIndexCoinController.reader store) (.remaining weights) pc.value hp := by
  rw [execution_eq_run h]
  exact run_state store fallback weights pc hp

theorem execution_bound {α : Type*} (D : ℕ) (hD : 0 < D) {store : Store} {fallback : α}
    {weights : WeightList α} (hUnit : UnitLattice D weights)
    {pc : FixedBinaryWord store.width} {hp : pc.value ≤ store.cap.value} {result : Result α store}
    {trace : List Event} (h : Execution store fallback weights pc hp result trace) :
    result.2 ≤ bound D weights.items.length store.width (result.1.2.value - pc.value) := by
  rw [execution_eq_run h]
  exact run_bound D hD store fallback weights hUnit pc hp

theorem reference_reindex {α : Type*} (seed : List Bool) (fallback : α) (weights : WeightList α)
    (N M : ℕ) (hNM : N = M) (pos : ℕ) (hp : pos ≤ N) (hq : pos ≤ M) :
    BinaryCategoricalRun.runIndexed fallback N (fun index => seed.getD index.val false) (.remaining weights) pos hp =
      BinaryCategoricalRun.runIndexed fallback M (fun index => seed.getD index.val false) (.remaining weights) pos hq := by
  subst M
  rfl

theorem run_prepared_seed {α : Type*} (seed : List Bool) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord (BinarySeedLookupTree.prepare seed).width) (hp : pc.value ≤ (BinarySeedLookupTree.prepare seed).cap.value) :
    decoded (BinarySeedLookupTree.prepare seed) (run (BinarySeedLookupTree.prepare seed) fallback weights pc hp) =
      BinaryCategoricalRun.runIndexed fallback seed.length (fun index => seed.getD index.val false)
        (.remaining weights) pc.value (by simpa only [cap_value] using hp) := by
  have h := run_state (BinarySeedLookupTree.prepare seed) fallback weights pc hp
  have hr : BinaryWordIndexCoinController.reader (BinarySeedLookupTree.prepare seed) = (fun index => seed.getD index.val false) := by
    funext index
    exact BinaryWordIndexCoinController.reader_prepare seed index
  rw [hr] at h
  exact h.trans (reference_reindex seed fallback weights _ _ (cap_value seed) pc.value hp
    (by simpa only [cap_value] using hp))


end Blotto.BinaryPRGWordControllerCategorical
