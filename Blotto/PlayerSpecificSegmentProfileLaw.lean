import Blotto.PlayerSpecificSegmentSampleLaw
import Blotto.PlayerSpecificFairLawAverage

/-! A descriptor may depend on a fresh outer scalar packet. The actual
two-packet draw has the same uniform branch-choice bound after averaging.
No finite support is enumerated by the executing sampler. -/
namespace Blotto.PlayerSpecificSegmentProfileLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law {N m : ℕ} (model : RationalCostModel) (root : Candidate) (H K : ℕ)
    (d : (Fin K → Bool) → Descriptor N (m+1)) (x : ℝ) : Mixed N :=
  (fairBitLaw ((m*H+K)+K)).map (fun bits =>
    values (PlayerSpecificAlgebraicSegmentSample.sample model root (d (secondBitBlock (m*H+K) K bits))
      (Fin.last m) H K (firstBitBlock (m*H+K) K bits)) x)

noncomputable def reference {N slots : ℕ} (K : ℕ) (l : (Fin K → Bool) → SegmentLottery N slots) : Mixed N :=
  averagedLaw (fairBitLaw K) (fun outer => (l outer).dyadicLaw K) (measurable_of_countable _)

theorem event_error {N m : ℕ} (model : RationalCostModel) (root : Candidate) (H K : ℕ)
    (d : (Fin K → Bool) → Descriptor N (m+1))
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (l : (Fin K → Bool) → SegmentLottery N (m+1))
    (hd : ∀ outer,PlayerSpecificAlgebraicDescriptorReference.Refines (d outer) x (l outer))
    (A : Set (Allocation N)) (hA : MeasurableSet A) :
    |(law model root H K d x : Measure (Allocation N)).real A-(reference K l : Measure (Allocation N)).real A|
      ≤ (m:ℝ)/(2:ℝ)^H := by
  have he : ∀ outer,
      |(PlayerSpecificSegmentSampleLaw.law model root (d outer) H K x : Measure (Allocation N)).real A-
        ((l outer).dyadicLaw K : Measure (Allocation N)).real A| ≤ (m:ℝ)/(2:ℝ)^H := by
    intro outer
    exact PlayerSpecificSegmentSampleLaw.event_error model root (d outer) H K hm hirr hv x hx (l outer) (hd outer) A hA
  have hav := PlayerSpecificFairAveraging.error K _ _ _ he
  rw [law,PlayerSpecificFairAveraging.event _ _ A hA,reference,PlayerSpecificFairLawAverage.event K _ A hA]
  rw [PlayerSpecificFairAveraging.swap (m*H+K) K (fun inner outer =>
    if values (PlayerSpecificAlgebraicSegmentSample.sample model root (d outer) (Fin.last m) H K inner) x ∈ A then (1:ℝ) else 0)]
  simp_rw [PlayerSpecificSegmentSampleLaw.law,PlayerSpecificFairAveraging.event _ _ A hA] at hav
  exact hav

theorem midpoint_CDF_error {N m : ℕ} (model : RationalCostModel) (root : Candidate) (H K : ℕ)
    (d : (Fin K → Bool) → Descriptor N (m+1))
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (l : (Fin K → Bool) → SegmentLottery N (m+1))
    (hd : ∀ outer,PlayerSpecificAlgebraicDescriptorReference.Refines (d outer) x (l outer)) :
    CDFClose (law model root H K d x) (reference K l) ((m:ℝ)/(2:ℝ)^H) := by
  intro j z
  change |(Measure.map (fun y : Allocation N => y j) (law model root H K d x : Measure (Allocation N))).real (Set.Iic z)-
    (Measure.map (fun y : Allocation N => y j) (reference K l : Measure (Allocation N))).real (Set.Iic z)| ≤ _
  rw [map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic,
    map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic]
  exact event_error model root H K d hm hirr hv x hx l hd _ ((measurable_pi_apply j) measurableSet_Iic)

end Blotto.PlayerSpecificSegmentProfileLaw
