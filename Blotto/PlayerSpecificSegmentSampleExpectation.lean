import Blotto.PlayerSpecificSegmentSelectedLaw
import Blotto.PlayerSpecificFairAveraging
import Blotto.DyadicSegmentLottery

/-! Bounded-test comparison of the executing algebraic segment draw with
the exact descriptor mixture using the same finite midpoint packet. -/
namespace Blotto.PlayerSpecificSegmentSampleExpectation
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem point {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (l : SegmentLottery N slots)
    (hd : PlayerSpecificAlgebraicDescriptorReference.Refines d x l) (K : ℕ) (slot : Fin slots) (bits : Fin K → Bool) :
    values (interpolate root d slot (dyadicMidpointSample K bits)) x=l.dyadicPoint K slot bits := by
  rw [interpolate_value root d slot _ x hx,hd.first,hd.second]
  rfl

theorem weighted_error {N m : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N (m+1)) (H K : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (l : SegmentLottery N (m+1)) (hd : PlayerSpecificAlgebraicDescriptorReference.Refines d x l)
    (f : Allocation N → ℝ) (hf : ∀ y,0 ≤ f y ∧ f y ≤ 1) :
    |(∫ bits,f (values (PlayerSpecificAlgebraicSegmentSample.sample model root d (Fin.last m) H K bits) x)
        ∂(fairBitLaw (m*H+K) : Measure (Fin (m*H+K) → Bool)))-
      (∑ slot,l.weight slot*(∫ bits,f (l.dyadicPoint K slot bits) ∂(fairBitLaw K : Measure (Fin K → Bool))))|
      ≤ (m:ℝ)/(2:ℝ)^H := by
  let a := fun scalar => ∫ choice,
    f (values (interpolate root d (PlayerSpecificAlgebraicSegmentSample.selected model root d (Fin.last m) H choice).1
      (dyadicMidpointSample K scalar)) x) ∂(fairBitLaw (m*H) : Measure (Fin (m*H) → Bool))
  let b := fun scalar => ∑ slot,l.weight slot*f (l.dyadicPoint K slot scalar)
  have he : ∀ scalar,|a scalar-b scalar| ≤ (m:ℝ)/(2:ℝ)^H := by
    intro scalar
    have h := PlayerSpecificSegmentSelectedLaw.reference_error model root d H hm hirr hv x hx l hd
      (fun slot => f (values (interpolate root d slot (dyadicMidpointSample K scalar)) x)) (fun _ => hf _)
    dsimp only [a,b]
    simp_rw [point root d x hx.1 l hd K] at h ⊢
    exact h
  have hav := PlayerSpecificFairAveraging.error K a b _ he
  have hb : (∫ scalar,b scalar ∂(fairBitLaw K : Measure (Fin K → Bool)))=
      ∑ slot,l.weight slot*(∫ bits,f (l.dyadicPoint K slot bits) ∂(fairBitLaw K : Measure (Fin K → Bool))) := by
    simp only [b,integral_finsetSum _ (fun _ _ => Integrable.of_finite),integral_const_mul]
  rw [hb] at hav
  change |(∫ bits,(fun choice scalar =>
      f (values (interpolate root d (PlayerSpecificAlgebraicSegmentSample.selected model root d (Fin.last m) H choice).1
        (dyadicMidpointSample K scalar)) x)) (firstBitBlock (m*H) K bits) (secondBitBlock (m*H) K bits)
      ∂(fairBitLaw (m*H+K) : Measure (Fin (m*H+K) → Bool)))-_| ≤ _
  rw [PlayerSpecificFairAveraging.swap (m*H) K (fun choice scalar =>
    f (values (interpolate root d (PlayerSpecificAlgebraicSegmentSample.selected model root d (Fin.last m) H choice).1
      (dyadicMidpointSample K scalar)) x))]
  exact hav

end Blotto.PlayerSpecificSegmentSampleExpectation
