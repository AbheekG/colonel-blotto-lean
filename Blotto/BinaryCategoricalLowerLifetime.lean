import Blotto.BinaryWordSegmentLifetimeBound
import Blotto.BinaryCategoricalFallback

/-! Actual deterministic categorical lower-leaf execution follows every traced
mass/guard/division preparation and then its suffix, even at probability one.
It consumes no coin bits; original weights derive the full retained bound. -/
namespace Blotto.BinaryCategoricalLowerLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryCategoricalPreparation BinaryCategoricalRun BinaryCategoricalUnitLattice
set_option maxHeartbeats 2000000

def chooseWithTrace {α : Type*} (fallback : α) (weights : WeightList α) : α × Trace :=
  let prepared := BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights
  match hPrepared : prepared.1 with
  | .done selected => (selected,wrap 24 2 [prepared.2])
  | .ask choice =>
      let later := chooseWithTrace fallback choice.rest
      (later.1,wrap 32 2 [prepared.2,later.2])
termination_by weights.items.length
decreasing_by
  have hWeights := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice hPrepared
  have hLength := rest_length choice
  rw [hWeights] at hLength
  omega

theorem chooseWithTrace_erasure {α : Type*} (fallback : α) (weights : WeightList α) :
    (chooseWithTrace fallback weights).1 = BinaryCategoricalFallback.choose fallback weights := by
  conv_lhs => unfold chooseWithTrace
  conv_rhs => unfold BinaryCategoricalFallback.choose
  rw [← BinaryQuadraticCategoricalLifetime.prepareWithTrace_erases fallback weights]
  dsimp only
  cases h : (BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).1 with
  | done selected => rfl
  | ask choice => exact chooseWithTrace_erasure fallback choice.rest
termination_by weights.items.length
decreasing_by
  have hWeights := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice h
  have hLength := rest_length choice
  rw [hWeights] at hLength
  omega

def stepEnvelope (D M : ℕ) : ℕ := BinaryWordCategoricalLifetimeBound.preparationEnvelope D M + 128

theorem chooseWithTrace_usage {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α)
    (weights : WeightList α) (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M) :
    usage (chooseWithTrace fallback weights).2 ≤ (weights.items.length+1) * stepEnvelope D M := by
  have hPrep := BinaryWordCategoricalLifetimeBound.preparation_usage D hD M fallback weights hUnit hLength
  conv_lhs => unfold chooseWithTrace
  dsimp only
  cases h : (BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).1 with
  | done selected =>
      have hw := wrap_usage 24 2 [(BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      have hScale : stepEnvelope D M ≤ (weights.items.length+1) * stepEnvelope D M := by nlinarith
      dsimp only
      unfold stepEnvelope at *
      omega
  | ask choice =>
      have hWeights := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice h
      have hChoice : UnitLattice D choice.weights := hWeights.symm ▸ hUnit
      have hRest := choice_rest_unit D choice hChoice
      have hLen := rest_length choice
      rw [hWeights] at hLen
      have hLater := chooseWithTrace_usage D hD M fallback choice.rest hRest (by omega)
      have hw := wrap_usage 32 2
        [(BinaryQuadraticCategoricalLifetime.prepareWithTrace fallback weights).2,
          (chooseWithTrace fallback choice.rest).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      dsimp only
      unfold stepEnvelope at *
      nlinarith
termination_by weights.items.length
decreasing_by
  have hWeights := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice h
  have hLen := rest_length choice
  rw [hWeights] at hLen
  omega

def sourcePreparationEnvelope (k s : ℕ) : ℕ :=
  let b := 1 + k*s
  (k+1) * (BinaryQuadraticLifetime.opcodeBound (1+2*b) + 8) + 2500*(2+2*b)^3 + 32 + k +
    (BinaryQuadraticLifetime.opcodeFrames (1+2*b) + 150*(2+2*b)^2 + 32) + 4

theorem preparation_source (D k s : ℕ) (hWidth : binaryWordWidth D ≤ 1 + k*s) :
    BinaryWordCategoricalLifetimeBound.preparationEnvelope D k ≤ sourcePreparationEnvelope k s := by
  unfold BinaryWordCategoricalLifetimeBound.preparationEnvelope
    BinaryQuadraticCategoricalLifetime.preparationBound BinaryQuadraticCategoricalLifetime.sumStepBound
    BinaryQuadraticCategoricalLifetime.arithmeticFrames BinaryQuadraticCategoricalLifetime.operandWidth
    sourcePreparationEnvelope BinaryQuadraticLifetime.opcodeBound BinaryQuadraticLifetime.opcodeFrames
  dsimp only
  gcongr

def segmentWithTrace {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) : Fin k × Trace :=
  let chosen := chooseWithTrace fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)
  (chosen.1,wrapList k (8*k+16) (k+4) [chosen.2])

theorem segmentWithTrace_erasure {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) :
    (segmentWithTrace prepared fallback).1 =
      BinaryCategoricalFallback.segment prepared.table prepared.canonical prepared.nonnegative fallback :=
  chooseWithTrace_erasure fallback _

def envelope (k s : ℕ) : ℕ := (k+1) * (sourcePreparationEnvelope k s + 128) + 10*k + 64

theorem segmentWithTrace_usage {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s) (fallback : Fin k) :
    usage (segmentWithTrace prepared fallback).2 ≤ envelope k s := by
  let D := BinaryStoredSegmentChoiceWork.denominator prepared.table
  have hD := BinaryStoredSegmentChoiceWork.denominator_positive prepared.table
  have hUnit := BinaryStoredSegmentChoiceWork.source_unit prepared source hR
  have hLength : (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative).items.length = k :=
    List.length_ofFn
  have hWidth := BinaryStoredSegmentChoiceWork.denominator_width prepared.table s
    (fun slot => by rw [hR.1 slot]; exact hHeight slot)
  have hChoose := chooseWithTrace_usage D hD k fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) hUnit hLength.le
  rw [hLength] at hChoose
  have hSource := Nat.mul_le_mul_left (k+1) (Nat.add_le_add_right (preparation_source D k s hWidth) 128)
  have hw := wrapList_usage k (8*k+16) (k+4)
    [(chooseWithTrace fallback (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (segmentWithTrace prepared fallback).2 ≤ _ at hw
  unfold envelope stepEnvelope at *
  omega

theorem all_prefix {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source)
    (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s) (fallback : Fin k) (borrowed steps : ℕ) :
    retainedHeap borrowed (segmentWithTrace prepared fallback).2 steps ≤ borrowed + envelope k s ∧
    framePeak ((segmentWithTrace prepared fallback).2.take steps) ≤ envelope k s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (segmentWithTrace_usage prepared source hR s hHeight fallback) borrowed steps

end Blotto.BinaryCategoricalLowerLifetime
