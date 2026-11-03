import Blotto.BinaryStoredSegmentChoiceWork

/-! The native deterministic lower-leaf fallback follows every original
preparation/suffix rule, including probability one and zero remaining mass.
Actual mass is retained once; its primitive price uses the fixed-D unit
invariant. No coin bits or per-choice caps are introduced. -/

namespace Blotto.BinaryCategoricalLowerLeafWork
open BinaryCategoricalPreparation BinaryCategoricalRun BinaryCategoricalPreparationWork
open BinaryCategoricalUnitLattice

def chooseWithWork {α : Type*} (fallback : α) (weights : WeightList α) : α × ℕ :=
  let prepared := prepareWithWork fallback weights
  match hs : prepared.1 with
  | .done value => (value, prepared.2 + 1)
  | .ask choice =>
      let later := chooseWithWork fallback choice.rest
      (later.1, prepared.2 + later.2 + 1)
termination_by weights.items.length
decreasing_by
  have hL := rest_length choice
  rw [prepared_choice_weights fallback weights choice hs] at hL
  omega

theorem chooseWithWork_state {α : Type*} (fallback : α) (weights : WeightList α) :
    (chooseWithWork fallback weights).1 = BinaryCategoricalFallback.choose fallback weights := by
  conv_lhs => unfold chooseWithWork
  conv_rhs => unfold BinaryCategoricalFallback.choose
  rw [← prepareWithWork_state fallback weights]
  dsimp only
  cases hs : (prepareWithWork fallback weights).1 with
  | done value => rfl
  | ask choice => exact chooseWithWork_state fallback choice.rest
termination_by weights.items.length
decreasing_by
  have hL := rest_length choice
  rw [prepared_choice_weights fallback weights choice hs] at hL
  omega

theorem chooseWithWork_bound {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α)
    (weights : WeightList α) (h : UnitLattice D weights) (hLength : weights.items.length ≤ M) :
    (chooseWithWork fallback weights).2 ≤ (weights.items.length + 1) * (preparationBound D M + 1) := by
  have hPrep := (prepareWithWork_bound D hD fallback weights h).trans
    (BinaryCategoricalRunWork.preparationBound_mono D hLength)
  unfold chooseWithWork
  dsimp only
  cases hs : (prepareWithWork fallback weights).1 with
  | done value =>
      dsimp only
      have hScale := Nat.mul_le_mul_right (preparationBound D M + 1) (show 1 ≤ weights.items.length + 1 by omega)
      nlinarith
  | ask choice =>
      dsimp only
      have hW := prepared_choice_weights fallback weights choice hs
      have hL := rest_length choice
      rw [hW] at hL
      have ih := chooseWithWork_bound D hD M fallback choice.rest
        (choice_rest_unit D choice (hW.symm ▸ h)) (by omega)
      nlinarith
termination_by weights.items.length
decreasing_by
  have hL := rest_length choice
  rw [prepared_choice_weights fallback weights choice hs] at hL
  omega

def bound (k s : ℕ) : ℕ :=
  (k + 1) * ((k + 1) * (12000 * (2 + 2 * (1 + k * s)) ^ 3) + 500 * (2 + 2 * (1 + k * s)) ^ 2 + 1)

def segmentWithWork {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) : Fin k × ℕ :=
  chooseWithWork fallback (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)

theorem segmentWithWork_state {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k) :
    (segmentWithWork prepared fallback).1 =
      BinaryCategoricalFallback.segment prepared.table prepared.canonical prepared.nonnegative fallback :=
  chooseWithWork_state fallback _

theorem segmentWithWork_bound {n k : ℕ} (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (source : RationalSegmentLottery n k) (hR : prepared.table.Refines source) (s : ℕ)
    (hH : ∀ slot, RationalHeight (source.weight slot) s) (fallback : Fin k) :
    (segmentWithWork prepared fallback).2 ≤ bound k s := by
  have hUnit := BinaryStoredSegmentChoiceWork.source_unit prepared source hR
  have hW := BinaryStoredSegmentChoiceWork.denominator_width prepared.table s (fun slot => by rw [hR.1 slot]; exact hH slot)
  have hLength : (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative).items.length = k :=
    List.length_ofFn
  have hChoose := chooseWithWork_bound (BinaryStoredSegmentChoiceWork.denominator prepared.table)
    (BinaryStoredSegmentChoiceWork.denominator_positive prepared.table) k fallback _ hUnit hLength.le
  rw [hLength] at hChoose
  apply hChoose.trans
  unfold preparationBound bound
  gcongr

end Blotto.BinaryCategoricalLowerLeafWork
