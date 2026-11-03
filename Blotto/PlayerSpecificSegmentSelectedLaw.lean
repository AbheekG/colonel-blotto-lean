import Blotto.PlayerSpecificSegmentEnumeration

/-! The actual cached descriptor selector realizes its full weight table
up to m*2^-H against every bounded slot test. Reference tables supply
normalization through their checked actual field refinement. -/
namespace Blotto.PlayerSpecificSegmentSelectedLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem weighted_error {N m : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N (m+1)) (H : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hn : ∀ j,0 ≤ realEvaluate (d.weights.read j) x) (hs : ∑ j,realEvaluate (d.weights.read j) x=1)
    (f : Fin (m+1) → ℝ) (hf : ∀ j,0 ≤ f j ∧ f j ≤ 1) :
    |(∫ bits,f (PlayerSpecificAlgebraicSegmentSample.selected model root d (Fin.last m) H bits).1
        ∂(fairBitLaw (m*H) : Measure (Fin (m*H) → Bool)))-
      (∑ j,realEvaluate (d.weights.read j) x*f j)| ≤ (m:ℝ)/(2:ℝ)^H := by
  let w := fun j => realEvaluate (d.weights.read j) x
  let remaining := PlayerSpecificAlgebraicField.constant root.polynomial 1
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hr : Reduced root.polynomial remaining := PlayerSpecificAlgebraicField.constant_reduced _ 1 hm hm0
  have he : realEvaluate remaining x=1 := by
    simpa only [Rat.cast_one] using PlayerSpecificAlgebraicField.constant_value root.polynomial 1 x hx.1
  have hnorm : PlayerSpecificSegmentIdealMean.Remaining w (PlayerSpecificSegmentEnumeration.items m) (realEvaluate remaining x) := by
    rw [he]
    exact PlayerSpecificSegmentEnumeration.remaining m w hn hs
  have h := PlayerSpecificSegmentDiscrepancy.normalized model root d.weights (Fin.last m) H
    (PlayerSpecificSegmentEnumeration.items m) remaining hm hirr hv x hx hr hnorm f hf
  rw [he,PlayerSpecificSegmentEnumeration.full_mean m w hn hs f] at h
  unfold PlayerSpecificSegmentExpectation.mean at h
  rw [PlayerSpecificSegmentEnumeration.length] at h
  exact h

theorem reference_error {N m : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N (m+1)) (H : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (l : SegmentLottery N (m+1)) (hd : PlayerSpecificAlgebraicDescriptorReference.Refines d x l)
    (f : Fin (m+1) → ℝ) (hf : ∀ j,0 ≤ f j ∧ f j ≤ 1) :
    |(∫ bits,f (PlayerSpecificAlgebraicSegmentSample.selected model root d (Fin.last m) H bits).1
        ∂(fairBitLaw (m*H) : Measure (Fin (m*H) → Bool)))-(∑ j,l.weight j*f j)| ≤ (m:ℝ)/(2:ℝ)^H := by
  have hn : ∀ j,0 ≤ realEvaluate (d.weights.read j) x := by intro j; rw [hd.weights]; exact l.nonnegative j
  have hs : (∑ j,realEvaluate (d.weights.read j) x)=1 := by
    have he : (∑ j,realEvaluate (d.weights.read j) x)=(∑ j,l.weight j) := Finset.sum_congr rfl (fun j _ => hd.weights j)
    exact he.trans l.mass
  have h := weighted_error model root d H hm hirr hv x hx hn hs f hf
  have he : (∑ j,realEvaluate (d.weights.read j) x*f j)=(∑ j,l.weight j*f j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hd.weights]
  rw [he] at h
  exact h

end Blotto.PlayerSpecificSegmentSelectedLaw
