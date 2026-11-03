import Blotto.BinaryQuadraticCategoricalMeasured
import Blotto.BinaryWordCoinMeasured
import Blotto.BinaryWordCategoricalLifetimeBound

/-! Complete categorical selection shares each measured preparation and coin
result, and recurses only on the reached unselected suffix. Exact old label,
exhaustion, Boolean cursor and full allocation trace are preserved. Unit-lattice
original weights derive source work; native model prices remain separate. -/

namespace Blotto.BinaryWordCategoricalMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryCategoricalPreparation BinaryCategoricalRun BinaryCategoricalUnitLattice
set_option autoImplicit false
set_option maxHeartbeats 3500000

set_option cleanup.letToHave false in
def runWithExtras {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (((Option α × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ :=
  let produced := BinaryQuadraticCategoricalMeasured.prepareWithExtras fallback weights
  let prepared := produced.1
  match hs : prepared.1.1 with
  | .done selected => ((((some selected,pc),wrap 16 2 [prepared.1.2]),prepared.2+4),produced.2)
  | .ask choice =>
      let coin := BinaryWordCoinMeasured.sample store choice.probability pc hp
      match coin.1.1.1 with
      | none => ((((none,coin.1.1.2),wrap 24 2 [prepared.1.2,coin.1.2]),prepared.2+coin.2+8),produced.2)
      | some true => ((((some choice.head.1,coin.1.1.2),wrap 24 2 [prepared.1.2,coin.1.2]),prepared.2+coin.2+8),produced.2)
      | some false =>
          let result := runWithExtras store fallback choice.rest coin.1.1.2
            (BinaryWordCoinMeasured.sample_position store choice.probability pc hp).2
          let later := result.1
          (((later.1.1,wrap 32 2 [prepared.1.2,coin.1.2,later.1.2]),prepared.2+coin.2+later.2+12),produced.2+result.2)
termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalMeasured.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

def run {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((Option α × FixedBinaryWord store.width) × Trace) × ℕ :=
  (runWithExtras store fallback weights pc hp).1

theorem runWithExtras_compat {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : (runWithExtras store fallback weights pc hp).1 = run store fallback weights pc hp := rfl

theorem run_record {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : run store fallback weights pc hp =
  let prepared := BinaryQuadraticCategoricalMeasured.prepare fallback weights
  match hs : prepared.1.1 with
  | .done selected => (((some selected,pc),wrap 16 2 [prepared.1.2]),prepared.2+4)
  | .ask choice =>
      let coin := BinaryWordCoinMeasured.sample store choice.probability pc hp
      match coin.1.1.1 with
      | none => (((none,coin.1.1.2),wrap 24 2 [prepared.1.2,coin.1.2]),prepared.2+coin.2+8)
      | some true => (((some choice.head.1,coin.1.1.2),wrap 24 2 [prepared.1.2,coin.1.2]),prepared.2+coin.2+8)
      | some false =>
          let later := run store fallback choice.rest coin.1.1.2
            (BinaryWordCoinMeasured.sample_position store choice.probability pc hp).2
          ((later.1.1,wrap 32 2 [prepared.1.2,coin.1.2,later.1.2]),prepared.2+coin.2+later.2+12) := by
  conv_lhs => unfold run runWithExtras
  dsimp only
  rw [BinaryQuadraticCategoricalMeasured.prepareWithExtras_compat]
  cases hs : (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.1 with
  | done selected => rfl
  | ask choice =>
      dsimp only
      cases hc : (BinaryWordCoinMeasured.sample store choice.probability pc hp).1.1.1 with
      | none => simp only [hc]
      | some branch => cases branch <;> simp only [hc,run]

theorem run_erases {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store fallback weights pc hp).1 = BinaryWordCategoricalLifetime.runWithTrace store fallback weights pc hp := by
  conv_lhs => rw [run_record]
  conv_rhs => unfold BinaryWordCategoricalLifetime.runWithTrace
  dsimp only
  rw [BinaryQuadraticCategoricalMeasured.prepare_erases]
  cases hs : (BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).1 with
  | done selected => rfl
  | ask choice =>
      dsimp only
      simp only [BinaryWordCoinMeasured.sample_erases]
      cases hc : (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).1.1 with
      | none => rfl
      | some branch =>
        cases branch
        · simp only [hc]
          have hLater := run_erases store fallback choice.rest
            (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).1.2
            (BinaryWordCoinLifetime.sampleWithTrace_position store choice.probability pc hp).2
          exact congrArg (fun output : (Option α × FixedBinaryWord store.width) × Trace =>
            (output.1,wrap 32 2 [(BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).2,
              (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).2,output.2])) hLater
        · simp only [hc]
termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem run_position {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store fallback weights pc hp).1.1.2.value ∧
      (run store fallback weights pc hp).1.1.2.value ≤ store.cap.value := by
  rw [run_erases]
  exact BinaryWordCategoricalLifetime.runWithTrace_position store fallback weights pc hp

def stepPrice (D M i seedCap : ℕ) : ℕ := BinaryQuadraticCategoricalMeasured.preparationPrice D M+
  BinaryWordCoinMeasured.samplePrice (5+8*binaryWordWidth D) i seedCap+16

theorem coin_work (store : BinarySeedLookupTree.Store) (word : SignedWord) (W : ℕ) (hW : width word ≤ W)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordCoinMeasured.sample store word pc hp).2 ≤ BinaryWordCoinMeasured.samplePrice W store.width store.cap.value := by
  have h := BinaryWordCoinMeasured.sample_work store word pc hp W hW
  have hm : BinaryWordCoinMeasured.samplePrice W store.width (store.cap.value-pc.value) ≤
      BinaryWordCoinMeasured.samplePrice W store.width store.cap.value := by
    unfold BinaryWordCoinMeasured.samplePrice
    gcongr
    exact Nat.sub_le _ _
  exact h.trans hm

theorem run_work {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (store : BinarySeedLookupTree.Store)
    (fallback : α) (weights : WeightList α) (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store fallback weights pc hp).2 ≤ (weights.items.length+1)*stepPrice D M store.width store.cap.value := by
  have hPrep := BinaryQuadraticCategoricalMeasured.prepare_work D hD M fallback weights hUnit hLength
  have hScale : stepPrice D M store.width store.cap.value ≤
      (weights.items.length+1)*stepPrice D M store.width store.cap.value := by nlinarith
  rw [run_record]
  dsimp only
  cases hs : (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.1 with
  | done selected => dsimp only; unfold stepPrice at *; omega
  | ask choice =>
      have hw := BinaryQuadraticCategoricalMeasured.prepared_choice_weights fallback weights choice hs
      have hChoice : UnitLattice D choice.weights := hw.symm ▸ hUnit
      have hCoin := coin_work store choice.probability (5+8*binaryWordWidth D)
        (choice_probability_width D hD choice hChoice) pc hp
      have hPosition := BinaryWordCoinMeasured.sample_position store choice.probability pc hp
      cases hc : (BinaryWordCoinMeasured.sample store choice.probability pc hp).1.1.1 with
      | none => simp only [hc]; unfold stepPrice at *; omega
      | some branch =>
        cases branch
        · simp only [hc]
          have hRest := choice_rest_unit D choice hChoice
          have hLen := rest_length choice
          rw [hw] at hLen
          have hLater := run_work D hD M store fallback choice.rest hRest (by omega)
            (BinaryWordCoinMeasured.sample store choice.probability pc hp).1.1.2 hPosition.2
          rw [hLen] at hLater
          have hS : (weights.items.length+1)*stepPrice D M store.width store.cap.value =
              weights.items.length*stepPrice D M store.width store.cap.value+stepPrice D M store.width store.cap.value := by ring
          rw [hS]
          unfold stepPrice at *
          omega
        · simp only [hc]; unfold stepPrice at *; omega
termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalMeasured.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem run_usage {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (store : BinarySeedLookupTree.Store)
    (fallback : α) (weights : WeightList α) (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (run store fallback weights pc hp).1.2 ≤
      (weights.items.length+1)*BinaryWordCategoricalLifetimeBound.stepEnvelope D M store.width store.cap.value := by
  rw [run_erases]
  exact BinaryWordCategoricalLifetimeBound.runWithTrace_usage D hD M store fallback weights hUnit hLength pc hp

theorem all_prefix {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (store : BinarySeedLookupTree.Store)
    (fallback : α) (weights : WeightList α) (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (run store fallback weights pc hp).1.2 steps ≤
      borrowed+(weights.items.length+1)*BinaryWordCategoricalLifetimeBound.stepEnvelope D M store.width store.cap.value ∧
    framePeak ((run store fallback weights pc hp).1.2.take steps) ≤
      (weights.items.length+1)*BinaryWordCategoricalLifetimeBound.stepEnvelope D M store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (run_usage D hD M store fallback weights hUnit hLength pc hp) borrowed steps

end Blotto.BinaryWordCategoricalMeasured
