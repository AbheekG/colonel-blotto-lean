import Blotto.BinaryCategoricalFallback
import Blotto.BinaryStoredSegmentChoiceWork

/-! The categorical lower fallback retains actual mass/guard/division
preparations and always follows the lower successor, including probability one.
An input-derived denominator lattice prices the complete structural path.
It draws no coins; metadata, storage and physical execution are separate. -/

namespace Blotto.BinaryCategoricalLowerFallbackWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryCategoricalPreparation BinaryCategoricalRun
open BinaryCategoricalPreparationWork BinaryCategoricalUnitLattice BinaryStoredOverlapEnvironment

def chooseWithWork {α : Type*} (fallback : α) (weights : WeightList α) : α × ℕ :=
  let prepared := prepareWithWork fallback weights
  match _he : prepared.1 with
  | .done result => (result,prepared.2)
  | .ask choice =>
      let later := chooseWithWork fallback choice.rest
      (later.1,prepared.2 + later.2)
termination_by weights.items.length
decreasing_by
  have h := rest_length choice
  rw [prepared_choice_weights fallback weights choice _he] at h
  omega

theorem chooseWithWork_state {α : Type*} (fallback : α) (weights : WeightList α) :
    (chooseWithWork fallback weights).1 = BinaryCategoricalFallback.choose fallback weights := by
  conv_lhs => unfold chooseWithWork
  conv_rhs => unfold BinaryCategoricalFallback.choose
  rw [← prepareWithWork_state fallback weights]
  dsimp only
  cases he : (prepareWithWork fallback weights).1 with
  | done result => rfl
  | ask choice => exact chooseWithWork_state fallback choice.rest
termination_by weights.items.length
decreasing_by
  have h := rest_length choice
  rw [prepared_choice_weights fallback weights choice he] at h
  omega

theorem chooseWithWork_bound {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α)
    (weights : WeightList α) (hUnit : UnitLattice D weights) (hLength : weights.items.length ≤ M) :
    (chooseWithWork fallback weights).2 ≤ (weights.items.length + 1) * preparationBound D M := by
  have hPrepare := (prepareWithWork_bound D hD fallback weights hUnit).trans
    (BinaryCategoricalRunWork.preparationBound_mono D hLength)
  conv_lhs => unfold chooseWithWork
  dsimp only
  cases he : (prepareWithWork fallback weights).1 with
  | done result => nlinarith
  | ask choice =>
      dsimp only
      have hWeights := prepared_choice_weights fallback weights choice he
      have hChoice : UnitLattice D choice.weights := hWeights.symm ▸ hUnit
      have hRest := choice_rest_unit D choice hChoice
      have hLen := rest_length choice
      rw [hWeights] at hLen
      have hLater := chooseWithWork_bound D hD M fallback choice.rest hRest (by omega)
      have hScale := Nat.mul_le_mul_right (preparationBound D M) (show choice.rest.items.length + 1 ≤ weights.items.length by omega)
      nlinarith
termination_by weights.items.length
decreasing_by
  have h := rest_length choice
  rw [prepared_choice_weights fallback weights choice he] at h
  omega

def segmentWithWork {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hN : ∀ slot, 0 ≤ value (table.weight.read slot)) (fallback : Fin k) : Fin k × ℕ :=
  chooseWithWork fallback (BinaryCategoricalFallback.storedWeights table hC hN)

theorem segmentWithWork_state {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hN : ∀ slot, 0 ≤ value (table.weight.read slot)) (fallback : Fin k) :
    (segmentWithWork table hC hN fallback).1 = BinaryCategoricalFallback.segment table hC hN fallback :=
  chooseWithWork_state fallback _

def bound (k s : ℕ) : ℕ := (k + 1) * ((k + 1) * (12000 * (2 + 2 * (1 + k * s)) ^ 3) +
  500 * (2 + 2 * (1 + k * s)) ^ 2)

theorem segmentWithWork_bound {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (hN : ∀ slot, 0 ≤ value (table.weight.read slot)) (source : RationalSegmentLottery n k)
    (hR : table.Refines source) (s : ℕ) (hH : ∀ slot, RationalHeight (source.weight slot) s) (fallback : Fin k) :
    (segmentWithWork table hC hN fallback).2 ≤ bound k s := by
  let prepared : BinaryStoredSegmentProgram.Prepared n k := ⟨table,hC,hN⟩
  let D := BinaryStoredSegmentChoiceWork.denominator table
  have hD := BinaryStoredSegmentChoiceWork.denominator_positive table
  have hUnit := BinaryStoredSegmentChoiceWork.source_unit prepared source hR
  have hLength : (BinaryCategoricalFallback.storedWeights table hC hN).items.length = k := List.length_ofFn
  have hWidth := BinaryStoredSegmentChoiceWork.denominator_width table s (fun slot => by rw [hR.1 slot]; exact hH slot)
  have hPrice := chooseWithWork_bound D hD k fallback (BinaryCategoricalFallback.storedWeights table hC hN) hUnit hLength.le
  change (segmentWithWork table hC hN fallback).2 ≤ _ at hPrice
  rw [hLength] at hPrice
  apply hPrice.trans
  unfold preparationBound bound D
  gcongr

end Blotto.BinaryCategoricalLowerFallbackWork
