import Blotto.PlayerSpecificSegmentSampleLaw
import Blotto.PlayerSpecificAlgebraicThreeDraw

/-! The actual three-variable draw, for either coordinate order and the
exceptional boundary case, approximates its checked exact coupling law. -/
namespace Blotto.PlayerSpecificThreeDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicThreeInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 3 :=
  (fairBitLaw (8*H+K)).map (fun bits => values (PlayerSpecificAlgebraicThreeDraw.draw model root a H K bits) x)

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : ThreeSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicUnorderedThree.Values a i x) :
    PlayerSpecificAlgebraicDescriptorReference.Refines (PlayerSpecificAlgebraicUnorderedThree.prepare model root a) x i.segmentLottery := by
  obtain ⟨hw,hP,hQ⟩ := PlayerSpecificAlgebraicUnorderedThree.fields model root a i hm hirr hv x hx ha
  exact ⟨hw,fun slot => funext (hP slot),fun slot => funext (hQ slot)⟩

theorem event_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : ThreeSpec)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicUnorderedThree.Values a i x) (A : Set (Allocation 3)) (hA : MeasurableSet A) :
    |(law model root a H K x : Measure (Allocation 3)).real A-
      (i.segmentLottery.dyadicLaw K : Measure (Allocation 3)).real A| ≤ 8/(2:ℝ)^H :=
  PlayerSpecificSegmentSampleLaw.event_error model root _ H K hm hirr hv x hx i.segmentLottery
    (refines model root a i hm hirr hv x hx ha) A hA

theorem CDF_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : ThreeSpec)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicUnorderedThree.Values a i x) :
    CDFClose (law model root a H K x) i.law (8/(2:ℝ)^H+1/(2*(2:ℝ)^K)) := by
  have h := PlayerSpecificSegmentSampleLaw.CDF_error model root _ H K hm hirr hv x hx i.segmentLottery
    (refines model root a i hm hirr hv x hx ha)
  have he : i.segmentLottery.law=i.law := ProbabilityMeasure.toMeasure_injective i.segmentLottery_law
  rw [he] at h
  exact h

end Blotto.PlayerSpecificThreeDrawLaw
