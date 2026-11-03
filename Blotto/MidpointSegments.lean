import Blotto.MidpointGrid
import Blotto.RealCDFDistance
import Blotto.SegmentLottery

/-! Actual finite midpoint versions of segment draws and segment lotteries.
Their discrepancy is uniform over all endpoints, including constant and
decreasing coordinate projections; their exact hard budget is preserved. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

noncomputable def midpointSegmentLaw {N n : ℕ} (hN : 0 < N) (P Q : Allocation n) : Mixed n :=
  (midpointLaw hN).map (segmentPoint P Q)

theorem midpointSegmentLaw_marginal {N n : ℕ} (hN : 0 < N) (P Q : Allocation n) (j : Fin n) :
    (marginal (midpointSegmentLaw hN P Q) j : Measure ℝ) =
      ((midpointLaw hN).map (affineLine (P j) (Q j)) : Measure ℝ) := by
  change Measure.map (fun x : Allocation n => x j)
    (Measure.map (segmentPoint P Q) (midpointLaw hN : Measure ℝ)) = _
  rw [Measure.map_map (measurable_pi_apply j) (measurable_segmentPoint P Q)]
  rfl

theorem midpointSegmentLaw_CDF_error {N n : ℕ} (hN : 0 < N) (P Q : Allocation n) :
    CDFClose (midpointSegmentLaw hN P Q) (segmentLaw P Q) (1 / (2 * (N : ℝ))) := by
  have hm : RealCDFClose (midpointLaw hN) unitUniform (1 / (2 * (N : ℝ))) := midpointLaw_CDF_error hN
  intro j z
  unfold closedCDF
  rw [midpointSegmentLaw_marginal, segmentLaw_marginal]
  exact hm.affine (P j) (Q j) z

theorem midpointSegmentLaw_constant_coordinate {N n : ℕ} (hN : 0 < N) (P Q : Allocation n)
    (j : Fin n) (hj : P j = Q j) :
    (marginal (midpointSegmentLaw hN P Q) j : Measure ℝ) = Measure.dirac (P j) := by
  rw [midpointSegmentLaw_marginal, ← hj]
  have hf : affineLine (P j) (P j) = fun _ => P j := by funext t; unfold affineLine; ring
  change Measure.map (affineLine (P j) (P j)) (midpointLaw hN : Measure ℝ) = _
  rw [hf, Measure.map_const, measure_univ, one_smul]

theorem midpointSegmentLaw_fullBudget {N n : ℕ} (hN : 0 < N) {B : ℝ} {P Q : Allocation n}
    (hP : FullBudget B P) (hQ : FullBudget B Q) :
    ∀ᵐ x ∂(midpointSegmentLaw hN P Q : Measure (Allocation n)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map (segmentPoint P Q) (midpointLaw hN : Measure ℝ), FullBudget B x
  rw [ae_map_iff (measurable_segmentPoint P Q).aemeasurable (measurable_fullBudget B)]
  exact (midpointLaw_supported hN).mono (fun _ ht => segment_fullBudget hP hQ ht)

theorem midpointSegmentPoint_fullBudget {N n : ℕ} (hN : 0 < N) {B : ℝ} {P Q : Allocation n}
    (hP : FullBudget B P) (hQ : FullBudget B Q) (j : Fin N) :
    FullBudget B (segmentPoint P Q (midpoint j)) :=
  segment_fullBudget hP hQ ⟨le_of_lt (midpoint_bounds hN j).1, le_of_lt (midpoint_bounds hN j).2⟩

theorem midpointSegmentLaw_inBox {N n : ℕ} (hN : 0 < N) {L P Q : Allocation n}
    (hP : InBox L P) (hQ : InBox L Q) :
    ∀ᵐ x ∂(midpointSegmentLaw hN P Q : Measure (Allocation n)), InBox L x := by
  change ∀ᵐ x ∂Measure.map (segmentPoint P Q) (midpointLaw hN : Measure ℝ), InBox L x
  rw [ae_map_iff (measurable_segmentPoint P Q).aemeasurable (measurable_inBox L)]
  exact (midpointLaw_supported hN).mono (fun _ ht => segment_inBox hP hQ ht)

theorem probabilityMixture_CDFClose {n k : ℕ} (weight : Fin k → ℝ) (μ ν : Fin k → Mixed n)
    (hw : ∀ i, 0 ≤ weight i) (hs : ∑ i, weight i = 1) {δ : ℝ} (h : ∀ i, CDFClose (μ i) (ν i) δ) :
    CDFClose (probabilityMixture weight μ hw hs) (probabilityMixture weight ν hw hs) δ := by
  intro j z
  have hc := mixture_RealCDFClose_constant weight (fun i => marginal (μ i) j) (fun i => marginal (ν i) j)
    hw hs (fun i t => h i j t) z
  have hm (law : Fin k → Mixed n) :
      (marginal (probabilityMixture weight law hw hs) j : Measure ℝ) =
        (probabilityMixture weight (fun i => marginal (law i) j) hw hs : Measure ℝ) :=
    probabilityMixture_marginal _ _ _ _ _
  unfold closedCDF
  rw [hm μ, hm ν]
  exact hc

namespace SegmentLottery

noncomputable def midpointLaw {n k N : ℕ} (l : SegmentLottery n k) (hN : 0 < N) : Mixed n :=
  probabilityMixture l.weight (fun i => midpointSegmentLaw hN (l.P i) (l.Q i)) l.nonnegative l.mass

theorem midpointLaw_CDF_error {n k N : ℕ} (l : SegmentLottery n k) (hN : 0 < N) :
    CDFClose (l.midpointLaw hN) l.law (1 / (2 * (N : ℝ))) :=
  probabilityMixture_CDFClose l.weight _ _ l.nonnegative l.mass
    (fun i => midpointSegmentLaw_CDF_error hN (l.P i) (l.Q i))

theorem midpointLaw_fullBudget {n k N : ℕ} (l : SegmentLottery n k) (hN : 0 < N) {B : ℝ}
    (h : ∀ i, FullBudget B (l.P i) ∧ FullBudget B (l.Q i)) :
    ∀ᵐ x ∂(l.midpointLaw hN : Measure (Allocation n)), FullBudget B x := by
  apply probabilityMixture_ae
  exact fun i => midpointSegmentLaw_fullBudget hN (h i).1 (h i).2

end SegmentLottery
end Blotto
