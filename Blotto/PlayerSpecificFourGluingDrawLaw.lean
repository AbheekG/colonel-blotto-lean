import Blotto.PlayerSpecificSegmentSampleLaw
import Blotto.PlayerSpecificAlgebraicFourGluingDraw

/-! The executing normal four-variable branch approximates its exact
overlap coupling. All 81 table slots, including padding, are included. -/
namespace Blotto.PlayerSpecificFourGluingDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 4 :=
  (fairBitLaw (80*H+K)).map (fun bits => values (PlayerSpecificAlgebraicFourGluingDraw.draw model root a H K bits) x)

theorem event_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (hcase : (1-i.p)*i.ell ≤ i.w) (A : Set (Allocation 4)) (hA : MeasurableSet A) :
    |(law model root a H K x : Measure (Allocation 4)).real A-
      ((i.gluingDescriptor hcase).dyadicLaw K : Measure (Allocation 4)).real A| ≤ 80/(2:ℝ)^H :=
  PlayerSpecificSegmentSampleLaw.event_error model root _ H K hm hirr hv x hx (i.gluingDescriptor hcase)
    (PlayerSpecificAlgebraicFourGluingTable.refines model root a i hm hirr hv x hx ha T hfit hml hmT hT hcase) A hA

theorem CDF_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (hcase : (1-i.p)*i.ell ≤ i.w) :
    CDFClose (law model root a H K x) (i.gluingCaseLaw hcase) (80/(2:ℝ)^H+1/(2*(2:ℝ)^K)) := by
  have h := PlayerSpecificSegmentSampleLaw.CDF_error model root _ H K hm hirr hv x hx (i.gluingDescriptor hcase)
    (PlayerSpecificAlgebraicFourGluingTable.refines model root a i hm hirr hv x hx ha T hfit hml hmT hT hcase)
  have he : (i.gluingDescriptor hcase).law=i.gluingCaseLaw hcase :=
    ProbabilityMeasure.toMeasure_injective (i.gluingDescriptor_law hcase)
  rw [he] at h
  exact h

end Blotto.PlayerSpecificFourGluingDrawLaw
