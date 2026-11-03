import Blotto.BinaryQuadraticCategoricalLifetime
import Blotto.BinaryWordCoinLifetime
import Blotto.BinaryPRGWordControllerDataCategorical
import Blotto.BinaryPRGHeapTraceUsage

/-! Actual quadratic categorical preparation and shared Boolean-PC coins.
The trace consumes its arithmetic and coin results, preserving the complete
selected label/none and absolute Boolean cursor. All regions remain retained. -/
namespace Blotto.BinaryWordCategoricalLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryCategoricalPreparation BinaryCategoricalRun
set_option maxHeartbeats 2000000

theorem preparation_erasure {α : Type*} (fallback : α) (weights : WeightList α) :
    (BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).1 =
      BinaryPRGWordControllerDataCategorical.prepare fallback weights :=
  (BinaryQuadraticCategoricalLifetime.prepareWithTrace_erases fallback weights).trans
    ((BinaryPRGWordControllerPreparation.prepareWithWork_state fallback weights).symm.trans
      (BinaryPRGWordControllerDataCategorical.prepare_erasure fallback weights))

def runWithTrace {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (Option α × FixedBinaryWord store.width) × Trace :=
  let prepared := BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights
  match hs : prepared.1 with
  | .done selected => ((some selected,pc),wrap 16 2 [prepared.2])
  | .ask choice =>
      let coin := BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp
      match coin.1.1 with
      | none => ((none,coin.1.2),wrap 24 2 [prepared.2,coin.2])
      | some true => ((some choice.head.1,coin.1.2),wrap 24 2 [prepared.2,coin.2])
      | some false =>
          let later := runWithTrace store fallback choice.rest coin.1.2
            (BinaryWordCoinLifetime.sampleWithTrace_position store choice.probability pc hp).2
          (later.1,wrap 32 2 [prepared.2,coin.2,later.2])
termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem runWithTrace_erasure {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runWithTrace store fallback weights pc hp).1 = BinaryPRGWordControllerDataCategorical.run store fallback weights pc hp := by
  conv_lhs => unfold runWithTrace
  conv_rhs => unfold BinaryPRGWordControllerDataCategorical.run
  dsimp only
  rw [preparation_erasure]
  cases hs : BinaryPRGWordControllerDataCategorical.prepare fallback weights with
  | done selected => rfl
  | ask choice =>
      dsimp only
      simp only [BinaryWordCoinLifetime.sampleWithTrace_erases]
      cases hc : (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).1 with
      | none => rfl
      | some branch =>
          cases branch
          · exact runWithTrace_erasure store fallback choice.rest
              (BinaryPRGWordControllerDataCoin.sample store choice.probability pc hp).2
              (BinaryPRGWordControllerDataCoin.sample_position store choice.probability pc hp).2
          · rfl
termination_by weights.items.length
decreasing_by
  have hw := BinaryPRGWordControllerDataCategorical.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem runWithTrace_position {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runWithTrace store fallback weights pc hp).1.2.value ∧
      (runWithTrace store fallback weights pc hp).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_erasure,← BinaryPRGWordControllerDataCategorical.run_erasure]
  exact BinaryPRGWordControllerCategorical.run_position_bounds store fallback weights pc hp

end Blotto.BinaryWordCategoricalLifetime
