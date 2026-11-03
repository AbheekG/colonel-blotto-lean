import Blotto.PlayerSpecificSegmentSampleExpectation
import Blotto.AllocationCDFDistance

/-! Actual finite-bit segment laws: the component-choice error holds for
every measurable allocation event. The additional midpoint error is a
marginal CDF bound, as required for the paper's payoff stability argument. -/
namespace Blotto.PlayerSpecificSegmentSampleLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law {N m : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N (m+1))
    (H K : ℕ) (x : ℝ) : Mixed N :=
  (fairBitLaw (m*H+K)).map (fun bits =>
    values (PlayerSpecificAlgebraicSegmentSample.sample model root d (Fin.last m) H K bits) x)

theorem dyadic_event {N slots : ℕ} (l : SegmentLottery N slots) (K : ℕ) (A : Set (Allocation N))
    (hA : MeasurableSet A) :
    (l.dyadicLaw K : Measure (Allocation N)).real A=
      ∑ slot,l.weight slot*(∫ bits,(if l.dyadicPoint K slot bits ∈ A then (1:ℝ) else 0)
        ∂(fairBitLaw K : Measure (Fin K → Bool))) := by
  unfold SegmentLottery.dyadicLaw
  rw [probabilityMixture_real_apply _ _ _ _ _ hA]
  apply Finset.sum_congr rfl
  intro slot _
  rw [dyadicSegmentLaw,PlayerSpecificFairAveraging.event K (dyadicSegmentPoint K (l.P slot) (l.Q slot)) A hA]
  rfl

theorem event_error {N m : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N (m+1)) (H K : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (l : SegmentLottery N (m+1)) (hd : PlayerSpecificAlgebraicDescriptorReference.Refines d x l)
    (A : Set (Allocation N)) (hA : MeasurableSet A) :
    |(law model root d H K x : Measure (Allocation N)).real A-(l.dyadicLaw K : Measure (Allocation N)).real A|
      ≤ (m:ℝ)/(2:ℝ)^H := by
  rw [law,PlayerSpecificFairAveraging.event _ _ A hA,dyadic_event l K A hA]
  exact PlayerSpecificSegmentSampleExpectation.weighted_error model root d H K hm hirr hv x hx l hd
    (fun y => if y ∈ A then 1 else 0) (fun y => by split <;> norm_num)

theorem midpoint_CDF_error {N m : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N (m+1)) (H K : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (l : SegmentLottery N (m+1)) (hd : PlayerSpecificAlgebraicDescriptorReference.Refines d x l) :
    CDFClose (law model root d H K x) (l.dyadicLaw K) ((m:ℝ)/(2:ℝ)^H) := by
  intro j z
  change |(Measure.map (fun y : Allocation N => y j) (law model root d H K x : Measure (Allocation N))).real (Set.Iic z)-
    (Measure.map (fun y : Allocation N => y j) (l.dyadicLaw K : Measure (Allocation N))).real (Set.Iic z)| ≤ _
  rw [map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic,
    map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic]
  exact event_error model root d H K hm hirr hv x hx l hd _ ((measurable_pi_apply j) measurableSet_Iic)

theorem CDF_error {N m : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N (m+1)) (H K : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (l : SegmentLottery N (m+1)) (hd : PlayerSpecificAlgebraicDescriptorReference.Refines d x l) :
    CDFClose (law model root d H K x) l.law ((m:ℝ)/(2:ℝ)^H+1/(2*(2:ℝ)^K)) :=
  (midpoint_CDF_error model root d H K hm hirr hv x hx l hd).triangle (l.dyadicLaw_CDF_error K)

end Blotto.PlayerSpecificSegmentSampleLaw
