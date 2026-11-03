import Blotto.BinaryWordCategoricalLifetime

/-! Unit-lattice source weights derive complete retained categorical usage.
The conservative envelope counts every old arithmetic/coin region, without
requiring reclamation or a probability-width/primitive-price oracle. -/
namespace Blotto.BinaryWordCategoricalLifetimeBound
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryCategoricalPreparation BinaryCategoricalRun BinaryCategoricalUnitLattice
open BinaryWordCategoricalLifetime
set_option maxHeartbeats 2000000

def preparationEnvelope (D M : ℕ) : ℕ :=
  BinaryQuadraticCategoricalLifetime.preparationBound D M + M +
    BinaryQuadraticCategoricalLifetime.arithmeticFrames D + 4

def coinEnvelope (W indexWidth seedCap : ℕ) : ℕ :=
  BinaryWordCoinLifetime.sampleBound W indexWidth seedCap + seedCap + 2 * W + 2 * indexWidth + 24

def stepEnvelope (D M indexWidth seedCap : ℕ) : ℕ :=
  preparationEnvelope D M + coinEnvelope (5 + 8 * binaryWordWidth D) indexWidth seedCap + 64

theorem preparation_usage {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α) (weights : WeightList α)
    (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M) :
    usage (BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).2 ≤ preparationEnvelope D M := by
  have h := BinaryQuadraticCategoricalLifetime.prepareWithTrace_bounds D hD M fallback weights hUnit hLength
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells preparationEnvelope
  omega

theorem coin_usage (store : BinarySeedLookupTree.Store) (word : SignedWord) (W : ℕ) (hW : width word ≤ W)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (BinaryWordCoinLifetime.sampleWithTrace store word pc hp).2 ≤ coinEnvelope W store.width store.cap.value := by
  have h := BinaryWordCoinLifetime.sampleWithTrace_bounds store word pc hp W hW
  have hRemain : store.cap.value - pc.value ≤ store.cap.value := Nat.sub_le _ _
  have hMono : BinaryWordCoinLifetime.sampleBound W store.width (store.cap.value - pc.value) ≤
      BinaryWordCoinLifetime.sampleBound W store.width store.cap.value := by
    unfold BinaryWordCoinLifetime.sampleBound
    gcongr
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells coinEnvelope
  omega

theorem runWithTrace_usage {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (store : BinarySeedLookupTree.Store)
    (fallback : α) (weights : WeightList α) (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (BinaryWordCategoricalLifetime.runWithTrace store fallback weights pc hp).2 ≤
      (weights.items.length + 1) * stepEnvelope D M store.width store.cap.value := by
  have hPrep := preparation_usage D hD M fallback weights hUnit hLength
  conv_lhs => unfold BinaryWordCategoricalLifetime.runWithTrace
  dsimp only
  cases hs : (BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).1 with
  | done selected =>
      have hw := wrap_usage 16 2 [(BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      have hm : stepEnvelope D M store.width store.cap.value ≤
          (weights.items.length + 1) * stepEnvelope D M store.width store.cap.value := by nlinarith
      dsimp only
      unfold stepEnvelope at *
      omega
  | ask choice =>
      have hwgt := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice hs
      have hChoice : UnitLattice D choice.weights := hwgt.symm ▸ hUnit
      have hProb := choice_probability_width D hD choice hChoice
      have hCoin := coin_usage store choice.probability (5 + 8 * binaryWordWidth D) hProb pc hp
      have hPosition := BinaryWordCoinLifetime.sampleWithTrace_position store choice.probability pc hp
      cases hc : (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).1.1 with
      | none =>
          simp only [hc]
          have hw := wrap_usage 24 2 [(BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).2,
            (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          have hm : stepEnvelope D M store.width store.cap.value ≤
              (weights.items.length + 1) * stepEnvelope D M store.width store.cap.value := by nlinarith
          unfold stepEnvelope at *
          omega
      | some branch =>
          cases branch
          · simp only [hc]
            have hRest := choice_rest_unit D choice hChoice
            have hLen := rest_length choice
            rw [hwgt] at hLen
            have hLater := runWithTrace_usage D hD M store fallback choice.rest hRest (by omega)
              (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).1.2 hPosition.2
            rw [hLen] at hLater
            have hw := wrap_usage 32 2 [(BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).2,
              (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).2,
              (BinaryWordCategoricalLifetime.runWithTrace store fallback choice.rest
                (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).1.2 hPosition.2).2]
            simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
            unfold stepEnvelope at *
            nlinarith
          · simp only [hc]
            have hw := wrap_usage 24 2 [(BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).2,
              (BinaryWordCoinLifetime.sampleWithTrace store choice.probability pc hp).2]
            simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
            have hm : stepEnvelope D M store.width store.cap.value ≤
                (weights.items.length + 1) * stepEnvelope D M store.width store.cap.value := by nlinarith
            unfold stepEnvelope at *
            omega
termination_by weights.items.length
decreasing_by
  have hwgt := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice hs
  have hLen := rest_length choice
  rw [hwgt] at hLen
  omega

theorem all_prefix {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (store : BinarySeedLookupTree.Store)
    (fallback : α) (weights : WeightList α) (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (BinaryWordCategoricalLifetime.runWithTrace store fallback weights pc hp).2 steps ≤
        borrowed + (weights.items.length + 1) * stepEnvelope D M store.width store.cap.value ∧
      framePeak ((BinaryWordCategoricalLifetime.runWithTrace store fallback weights pc hp).2.take steps) ≤
        (weights.items.length + 1) * stepEnvelope D M store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage D hD M store fallback weights hUnit hLength pc hp) borrowed steps

end Blotto.BinaryWordCategoricalLifetimeBound
