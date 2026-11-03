import Blotto.PlayerSpecificResourceHybrid
import Blotto.FourDyadicCoupling

/-! The actual merged four-variable branch approximates the same
finite-midpoint exact-choice law for every H. -/
namespace Blotto.PlayerSpecificFourMergedHybrid
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem event_bound (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) :
    PlayerSpecificEventDistance.Bound (PlayerSpecificFourMergedDrawLaw.law RationalCostModel.schoolbook r.root a H K x)
      (i.smallUniformDyadicLaw hcase K) (8/(2:ℝ)^H) := by
  have hp := PlayerSpecificAlgebraicFourMergedInput.values RationalCostModel.schoolbook r.root a i hm hirr hv x hx ha T hfit hcase
  rw [PlayerSpecificFourMergedDrawLaw.law_eq RationalCostModel.schoolbook r.root a i hm hirr hv x hx ha T hfit hcase H K]
  have h : PlayerSpecificEventDistance.Bound (PlayerSpecificThreeDrawLaw.law RationalCostModel.schoolbook r.root
      (PlayerSpecificAlgebraicFourMergedInput.prepare RationalCostModel.schoolbook r.root a).child H K x)
      ((i.smallUniformInput hcase).childSpec.segmentLottery.dyadicLaw K) (8/(2:ℝ)^H) :=
    fun A hA => PlayerSpecificThreeDrawLaw.event_error RationalCostModel.schoolbook r.root _ (i.smallUniformInput hcase).childSpec
      H K hm hirr hv x hx hp.2.2 A hA
  exact PlayerSpecificEventDistance.map _ _ _ h (splitFirstTwo (i.smallUniformInput hcase).l0 (i.smallUniformInput hcase).l1)
    (measurable_splitFirstTwo _ _)

end Blotto.PlayerSpecificFourMergedHybrid
