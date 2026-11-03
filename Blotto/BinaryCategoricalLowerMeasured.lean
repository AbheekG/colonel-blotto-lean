import Blotto.BinaryQuadraticCategoricalMeasured
import Blotto.BinaryCategoricalLowerLifetime

/-! Deterministic lower selection executes actual measured mass/guard/division
preparation and every reached suffix, without a coin input. Exact preceding
selection/trace and original-weight-derived source bounds are retained. -/
namespace Blotto.BinaryCategoricalLowerMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryCategoricalPreparation BinaryCategoricalRun BinaryCategoricalUnitLattice
set_option autoImplicit false
set_option maxHeartbeats 1500000

set_option cleanup.letToHave false in
def chooseWithExtras {α : Type*} (fallback : α) (weights : WeightList α) : ((α × Trace) × ℕ) × ℕ :=
  let produced := BinaryQuadraticCategoricalMeasured.prepareWithExtras fallback weights
  let prepared := produced.1
  match hPrepared : prepared.1.1 with
  | .done selected => (((selected,wrap 24 2 [prepared.1.2]),prepared.2+4),produced.2)
  | .ask choice =>
      let result := chooseWithExtras fallback choice.rest
      let later := result.1
      (((later.1.1,wrap 32 2 [prepared.1.2,later.1.2]),prepared.2+later.2+8),produced.2+result.2)
termination_by weights.items.length
decreasing_by
  have hWeights := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice
    (by rw [← BinaryQuadraticCategoricalMeasured.prepare_erases]; exact hPrepared)
  have hLength := rest_length choice
  rw [hWeights] at hLength
  omega

def choose {α : Type*} (fallback : α) (weights : WeightList α) : (α × Trace) × ℕ :=
  (chooseWithExtras fallback weights).1

theorem chooseWithExtras_compat {α : Type*} (fallback : α) (weights : WeightList α) : (chooseWithExtras fallback weights).1 = choose fallback weights := rfl

theorem choose_record {α : Type*} (fallback : α) (weights : WeightList α) : choose fallback weights =
  let prepared := BinaryQuadraticCategoricalMeasured.prepare fallback weights
  match hPrepared : prepared.1.1 with
  | .done selected => ((selected,wrap 24 2 [prepared.1.2]),prepared.2+4)
  | .ask choice =>
      let later := choose fallback choice.rest
      ((later.1.1,wrap 32 2 [prepared.1.2,later.1.2]),prepared.2+later.2+8) := by
  conv_lhs => unfold choose chooseWithExtras
  dsimp only
  rw [BinaryQuadraticCategoricalMeasured.prepareWithExtras_compat]
  cases h : (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.1 with
  | done selected => rfl
  | ask choice => simp only [choose]


theorem choose_erases {α : Type*} (fallback : α) (weights : WeightList α) :
    (choose fallback weights).1 = BinaryCategoricalLowerLifetime.chooseWithTrace fallback weights := by
  conv_lhs => rw [choose_record]
  conv_rhs => unfold BinaryCategoricalLowerLifetime.chooseWithTrace
  rw [← BinaryQuadraticCategoricalMeasured.prepare_erases]
  dsimp only
  cases h : (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.1 with
  | done selected => rfl
  | ask choice => simp only [choose_erases fallback choice.rest]
termination_by weights.items.length
decreasing_by
  have hWeights := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice
    (by rw [← BinaryQuadraticCategoricalMeasured.prepare_erases]; exact h)
  have hLength := rest_length choice
  rw [hWeights] at hLength
  omega

def stepPrice (D M : ℕ) : ℕ := BinaryQuadraticCategoricalMeasured.preparationPrice D M+8

theorem choose_work {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α) (weights : WeightList α)
    (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M) :
    (choose fallback weights).2 ≤ (weights.items.length+1)*stepPrice D M := by
  have hPrep := BinaryQuadraticCategoricalMeasured.prepare_work D hD M fallback weights hUnit hLength
  conv_lhs => rw [choose_record]
  dsimp only
  cases h : (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.1 with
  | done selected =>
      dsimp only
      unfold stepPrice
      nlinarith
  | ask choice =>
      have hWeights := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice
        (by rw [← BinaryQuadraticCategoricalMeasured.prepare_erases]; exact h)
      have hChoice : UnitLattice D choice.weights := hWeights.symm ▸ hUnit
      have hRest := choice_rest_unit D choice hChoice
      have hLen := rest_length choice
      rw [hWeights] at hLen
      have hLater := choose_work D hD M fallback choice.rest hRest (by omega)
      dsimp only
      unfold stepPrice at *
      nlinarith
termination_by weights.items.length
decreasing_by
  have hWeights := BinaryQuadraticCategoricalLifetime.prepared_choice_weights fallback weights choice
    (by rw [← BinaryQuadraticCategoricalMeasured.prepare_erases]; exact h)
  have hLen := rest_length choice
  rw [hWeights] at hLen
  omega

def sourcePreparationPrice (k s : ℕ) : ℕ :=
  let b := 1+k*s
  (k+1)*(11000*(1+2*b+1)^2+8)+BinaryQuadraticExpression.uniformPrice b+32

theorem preparation_source (D k s : ℕ) (hWidth : binaryWordWidth D ≤ 1+k*s) :
    BinaryQuadraticCategoricalMeasured.preparationPrice D k ≤ sourcePreparationPrice k s := by
  unfold BinaryQuadraticCategoricalMeasured.preparationPrice BinaryQuadraticCategoricalMeasured.sumStepPrice
    BinaryQuadraticCategoricalMeasured.operandWidth sourcePreparationPrice BinaryQuadraticExpression.uniformPrice
  dsimp only
  gcongr

set_option cleanup.letToHave false in
def segmentWithExtras {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) : ((Fin k × Trace) × ℕ) × ℕ :=
  let produced := chooseWithExtras fallback (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)
  let chosen := produced.1
  (((chosen.1.1,wrapList k (8*k+16) (k+4) [chosen.1.2]),chosen.2+16*(k+1)^2+8),produced.2)

def segment {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) : (Fin k × Trace) × ℕ :=
  (segmentWithExtras prepared fallback).1

theorem segmentWithExtras_compat {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) : (segmentWithExtras prepared fallback).1 = segment prepared fallback := rfl

theorem segment_record {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) : segment prepared fallback =
  let chosen := choose fallback (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)
  ((chosen.1.1,wrapList k (8*k+16) (k+4) [chosen.1.2]),chosen.2+16*(k+1)^2+8) := by
  rfl

theorem segment_erases {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) :
    (segment prepared fallback).1 = BinaryCategoricalLowerLifetime.segmentWithTrace prepared fallback := by
  simp only [segment_record,BinaryCategoricalLowerLifetime.segmentWithTrace,choose_erases]

def workEnvelope (k s : ℕ) : ℕ := (k+1)*(sourcePreparationPrice k s+8)+16*(k+1)^2+8

theorem segment_work {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (source : RationalSegmentLottery n k)
    (hR : prepared.table.Refines source) (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s) (fallback : Fin k) :
    (segment prepared fallback).2 ≤ workEnvelope k s := by
  let weights := NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative
  let D := BinaryStoredSegmentChoiceWork.denominator prepared.table
  have hD := BinaryStoredSegmentChoiceWork.denominator_positive prepared.table
  have hUnit := BinaryStoredSegmentChoiceWork.source_unit prepared source hR
  have hLength : weights.items.length = k := List.length_ofFn
  have hWidth := BinaryStoredSegmentChoiceWork.denominator_width prepared.table s (fun slot => by rw [hR.1 slot]; exact hHeight slot)
  have hChoose := choose_work D hD k fallback weights hUnit (by rw [hLength])
  rw [hLength] at hChoose
  have hPrice := preparation_source D k s hWidth
  have hScale := Nat.mul_le_mul_left (k+1) (Nat.add_le_add_right hPrice 8)
  change (choose fallback weights).2+16*(k+1)^2+8 ≤ _
  unfold workEnvelope stepPrice at *
  omega

theorem segment_bounds {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (source : RationalSegmentLottery n k)
    (hR : prepared.table.Refines source) (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s) (fallback : Fin k) :
    (segment prepared fallback).2 ≤ workEnvelope k s ∧ usage (segment prepared fallback).1.2 ≤ BinaryCategoricalLowerLifetime.envelope k s := by
  refine ⟨segment_work prepared source hR s hHeight fallback,?_⟩
  rw [segment_erases]
  exact BinaryCategoricalLowerLifetime.segmentWithTrace_usage prepared source hR s hHeight fallback

theorem all_prefix {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (source : RationalSegmentLottery n k)
    (hR : prepared.table.Refines source) (s : ℕ) (hHeight : ∀ slot,RationalHeight (source.weight slot) s) (fallback : Fin k) (borrowed steps : ℕ) :
    retainedHeap borrowed (segment prepared fallback).1.2 steps ≤ borrowed+BinaryCategoricalLowerLifetime.envelope k s ∧
      framePeak ((segment prepared fallback).1.2.take steps) ≤ BinaryCategoricalLowerLifetime.envelope k s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (segment_bounds prepared source hR s hHeight fallback).2 borrowed steps

end Blotto.BinaryCategoricalLowerMeasured
