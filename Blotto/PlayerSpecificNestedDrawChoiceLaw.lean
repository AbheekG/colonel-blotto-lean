import Blotto.PlayerSpecificSegmentProfileLaw
import Blotto.PlayerSpecificAlgebraicNestedSpecDraw

/-! Actual nested draws, including q=0/1 and restored coordinate order,
have a whole-event choice error of at most 17*2^-H. -/
namespace Blotto.PlayerSpecificNestedDrawChoiceLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def interiorLaw (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 3 :=
  (fairBitLaw ((17*H+K)+K)).map (fun bits => values (PlayerSpecificAlgebraicNestedInteriorDraw.draw model root a H K bits) x)

noncomputable def law (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 3 :=
  (fairBitLaw ((17*H+K)+K)).map (fun bits => values (PlayerSpecificAlgebraicNestedSpecDraw.draw model root a H K bits) x)

theorem interior_event_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (A : Set (Allocation 3)) (hA : MeasurableSet A) :
    |(interiorLaw model root a H K x : Measure (Allocation 3)).real A-
      (PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedInteriorProfile.reference i K) : Measure (Allocation 3)).real A|
        ≤ 17/(2:ℝ)^H :=
  PlayerSpecificSegmentProfileLaw.event_error model root H K (PlayerSpecificAlgebraicNestedInteriorProfile.prepare model root a K)
    hm hirr hv x hx (PlayerSpecificAlgebraicNestedInteriorProfile.reference i K)
    (PlayerSpecificAlgebraicNestedInteriorProfile.refines model root a i hm hirr hv x hx ha T hfit hml hmT hT K) A hA

theorem event_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedSpecInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (A : Set (Allocation 3)) (hA : MeasurableSet A) :
    |(law model root a H K x : Measure (Allocation 3)).real A-
      (PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedSpecProfile.reference i K) : Measure (Allocation 3)).real A|
        ≤ 17/(2:ℝ)^H :=
  PlayerSpecificSegmentProfileLaw.event_error model root H K (PlayerSpecificAlgebraicNestedSpecProfile.prepare model root a K)
    hm hirr hv x hx (PlayerSpecificAlgebraicNestedSpecProfile.reference i K)
    (PlayerSpecificAlgebraicNestedSpecProfile.refines model root a i hm hirr hv x hx ha T hfit hml hmT hT K) A hA

theorem midpoint_CDF_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedSpecInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    CDFClose (law model root a H K x)
      (PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedSpecProfile.reference i K)) (17/(2:ℝ)^H) :=
  PlayerSpecificSegmentProfileLaw.midpoint_CDF_error model root H K (PlayerSpecificAlgebraicNestedSpecProfile.prepare model root a K)
    hm hirr hv x hx (PlayerSpecificAlgebraicNestedSpecProfile.reference i K)
    (PlayerSpecificAlgebraicNestedSpecProfile.refines model root a i hm hirr hv x hx ha T hfit hml hmT hT K)

end Blotto.PlayerSpecificNestedDrawChoiceLaw
