import Blotto.GeneralPaperContinuousLiftContract
import Blotto.GeneralPaperSelectedCoordinatePayoff

/-! The paper's midpoint shifts compared directly with continuous rotation.
Both CDF conventions include ties, zero bids and repeated selected cells. -/
namespace Blotto.GeneralPaperContinuousFiniteShiftCDF
open MeasureTheory Set
open GeneralPaperContinuousUniformCells GeneralPaperSelectedShift
open GeneralPaperCircleFiniteAverage
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem uniform_index_points (D : ℕ) (hD : 0 < D) (points : Fin D → ℝ) :
    unitUniform.map (fun u => points (index D hD u)) = finiteUniformPoints hD points := by
  have hm : Measurable points := measurable_of_countable _
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (points ∘ index D hD) (unitUniform : Measure ℝ) = _
  rw [← Measure.map_map hm (measurable_index D hD), index_law]
  change Measure.map points (mixtureMeasure (fun _ : Fin D => 1/(D : ℝ))
    (fun i => RealThresholdChoice.pointLaw i)) = _
  rw [mixtureMeasure_map _ _ _ hm]
  change Measure.sum _ = Measure.sum _
  congr 1
  funext i
  change ENNReal.ofReal (1/(D : ℝ)) • Measure.map points (Measure.dirac i) = _
  rw [Measure.map_dirac' hm]
  rfl

noncomputable def continuous {h g : ℕ} (R W : ℕ) (weights : Fin g → ℕ)
    (x : Allocation (h+R)) (j : Fin g) : ProbabilityMeasure ℝ :=
  unitUniform.map (fun u => GeneralPaperContinuousCircleLaw.row R W weights x u (Fin.natAdd h j))

noncomputable def selectedLaw {h g : ℕ} (R W S : ℕ) (hR : 0 < R) (hW : 0 < W) (hS : 0 < S)
    (weights : Fin g → ℕ) (x : Allocation (h+R)) (j : Fin g) : ProbabilityMeasure ℝ :=
  finiteUniformPoints hS (fun l => GeneralPaperContinuousCircleLaw.row R W weights x
    (center (R*W) S (Nat.mul_pos hR hW) hS l) (Fin.natAdd h j))

theorem continuous_law {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (x : Allocation (h+R)) (j : Fin g) :
    continuous R W weights x j = finiteUniformPoints (Nat.mul_pos hR hW)
      (fun c => GeneralPaperCircleCanonicalLift.row R W hR hW weights x c.val (Fin.natAdd h j)) := by
  calc
    _ = unitUniform.map (fun u => GeneralPaperCircleCanonicalLift.row R W hR hW weights x
        (index (R*W) (Nat.mul_pos hR hW) u).val (Fin.natAdd h j)) := by
      apply ProbabilityMeasure.toMeasure_injective
      apply Measure.map_congr
      filter_upwards [GeneralPaperContinuousCircleLaw.row_ae R W hR hW weights hp] with u hu
      exact congrFun (hu x) (Fin.natAdd h j)
    _ = _ := uniform_index_points (R*W) (Nat.mul_pos hR hW)
      (fun c => GeneralPaperCircleCanonicalLift.row R W hR hW weights x c.val (Fin.natAdd h j))

theorem center_row {h g : ℕ} (R W S : ℕ) (hR : 0 < R) (hW : 0 < W) (hS : 0 < S)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (x : Allocation (h+R)) (l : Fin S) :
    GeneralPaperContinuousCircleLaw.row R W weights x (center (R*W) S (Nat.mul_pos hR hW) hS l) =
      GeneralPaperCircleCanonicalLift.row R W hR hW weights x
        (selected (R*W) S (Nat.mul_pos hR hW) hS l).val := by
  have hi := center_interior (R*W) S (Nat.mul_pos hR hW) hS l
  have hD : (0 : ℝ) < (R*W : ℕ) := by exact_mod_cast Nat.mul_pos hR hW
  apply GeneralPaperContinuousCircleLaw.row_on_cell R W hR hW weights hp x _ _
  constructor
  · simpa only [mul_comm] using (div_lt_iff₀ hD).mp hi.1
  · simpa only [mul_comm] using (lt_div_iff₀ hD).mp hi.2

theorem selected_law {h g : ℕ} (R W S : ℕ) (hR : 0 < R) (hW : 0 < W) (hS : 0 < S)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (x : Allocation (h+R)) (j : Fin g) :
    selectedLaw R W S hR hW hS weights x j = finiteUniformPoints hS
      (fun l => GeneralPaperCircleCanonicalLift.row R W hR hW weights x
        (selected (R*W) S (Nat.mul_pos hR hW) hS l).val (Fin.natAdd h j)) := by
  unfold selectedLaw
  congr 1
  funext l
  exact congrFun (center_row R W S hR hW hS weights hp x l) (Fin.natAdd h j)

theorem paper_finite_shifts {h g : ℕ} (R W S : ℕ) (hR : 0 < R) (hW : 0 < W) (hS : 0 < S)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (hs : ∑ j, weights j = W)
    (x : Allocation (h+R)) (j : Fin g) (t : ℝ) :
    |(selectedLaw R W S hR hW hS weights x j : Measure ℝ).real (Iio t) -
      (continuous R W weights x j : Measure ℝ).real (Iio t)| ≤ 1/(S : ℝ) ∧
    |(selectedLaw R W S hR hW hS weights x j : Measure ℝ).real (Iic t) -
      (continuous R W weights x j : Measure ℝ).real (Iic t)| ≤ 1/(S : ℝ) := by
  have hj : weights j ≤ W := by
    rw [← hs]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let reps := GeneralPaperCircleSortedComparison.sorted (GeneralPaperCircleCanonicalLift.representatives x)
  let points := fun a => GeneralPaperCircleCoordinatePayoff.coefficient R W (weights j)*reps a
  have hm : Monotone points := fun a b hab => mul_le_mul_of_nonneg_left
    (GeneralPaperCircleSortedComparison.sorted_monotone _ hab)
    (GeneralPaperCircleCoordinatePayoff.coefficient_nonnegative R W (weights j))
  let offset := GeneralPaperCircleArcPartition.before (GeneralPaperCircleHardBudget.lengths R weights) j.val
  have hStrict := GeneralPaperSelectedBidCDF.strict_error R W S hR hW hS (R*weights j) offset
    (Nat.mul_le_mul_left R hj) points hm t
  have hWeak := GeneralPaperSelectedBidCDF.weak_error R W S hR hW hS (R*weights j) offset
    (Nat.mul_le_mul_left R hj) points hm t
  have he (c : Fin (R*W)) : GeneralPaperSelectedBidCDF.point R W hR hW (R*weights j) offset points c =
      GeneralPaperCircleHardBudget.bid R W hR hW weights reps c.val j :=
    (GeneralPaperSelectedCoordinatePayoff.bid_point R W hR hW weights reps j c).symm
  simp_rw [he] at hStrict hWeak
  rw [selected_law R W S hR hW hS weights hp x j, continuous_law R W hR hW weights hp x j]
  rw [finiteUniformPoints_event hS _ (Iio t) measurableSet_Iio,
    finiteUniformPoints_event (Nat.mul_pos hR hW) _ (Iio t) measurableSet_Iio,
    finiteUniformPoints_event hS _ (Iic t) measurableSet_Iic,
    finiteUniformPoints_event (Nat.mul_pos hR hW) _ (Iic t) measurableSet_Iic]
  simp only [mem_Iio, mem_Iic, GeneralPaperCircleCanonicalLift.row,
    GeneralPaperCircleHardBudget.reconstruct_light]
  exact ⟨abs_le.mpr hStrict, abs_le.mpr hWeak⟩

end Blotto.GeneralPaperContinuousFiniteShiftCDF
