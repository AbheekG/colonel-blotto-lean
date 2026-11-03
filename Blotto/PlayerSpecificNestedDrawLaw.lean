import Blotto.PlayerSpecificNestedDrawChoiceLaw
import Blotto.PlayerSpecificNestedDyadicReference

/-! Complete marginal CDF bound for the actual nested finite-bit draw,
with both midpoint packets, actual conditional coins and all closed cases. -/
namespace Blotto.PlayerSpecificNestedDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem event_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedSpecInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (A : Set (Allocation 3)) (hA : MeasurableSet A) :
    |(PlayerSpecificNestedDrawChoiceLaw.law model root a H K x : Measure (Allocation 3)).real A-
      (i.dyadicLaw K : Measure (Allocation 3)).real A| ≤ 17/(2:ℝ)^H := by
  have h := PlayerSpecificNestedDrawChoiceLaw.event_error model root a i H K hm hirr hv x hx ha T hfit hml hmT hT A hA
  rw [PlayerSpecificNestedDyadicReference.spec] at h
  exact h

theorem CDF_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (H K : ℕ) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedSpecInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    CDFClose (PlayerSpecificNestedDrawChoiceLaw.law model root a H K x) i.law
      (17/(2:ℝ)^H+3/(2*(2:ℝ)^K)) := by
  have h := PlayerSpecificNestedDrawChoiceLaw.midpoint_CDF_error model root a i H K hm hirr hv x hx ha T hfit hml hmT hT
  rw [PlayerSpecificNestedDyadicReference.spec] at h
  exact h.triangle (i.dyadicLaw_CDF_error K)

end Blotto.PlayerSpecificNestedDrawLaw
