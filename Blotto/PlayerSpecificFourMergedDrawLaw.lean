import Blotto.PlayerSpecificThreeDrawLaw
import Blotto.PlayerSpecificAlgebraicFourMergedDraw
import Blotto.FourDyadicTransport

/-! The actual merged branch splits the complete three-variable sample.
Its whole law and marginal CDF bounds preserve this dependence. -/
namespace Blotto.PlayerSpecificFourMergedDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 4 :=
  (fairBitLaw (8*H+K)).map (fun bits => values (PlayerSpecificAlgebraicFourMergedDraw.draw model root a H K bits) x)

theorem law_eq (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) :
    law model root a H K x=splitLaw (i.smallUniformInput hcase).l0 (i.smallUniformInput hcase).l1
      (PlayerSpecificThreeDrawLaw.law model root (PlayerSpecificAlgebraicFourMergedInput.prepare model root a).child H K x) := by
  have hp := PlayerSpecificAlgebraicFourMergedInput.values model root a i hm hirr hv x hx ha T hfit hcase
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits => values (PlayerSpecificAlgebraicFourMergedDraw.draw model root a H K bits) x) _=
    Measure.map (splitFirstTwo (i.smallUniformInput hcase).l0 (i.smallUniformInput hcase).l1)
      (Measure.map (fun bits => values (PlayerSpecificAlgebraicThreeDraw.draw model root
        (PlayerSpecificAlgebraicFourMergedInput.prepare model root a).child H K bits) x)
          (fairBitLaw (8*H+K) : Measure (Fin (8*H+K) → Bool)))
  rw [Measure.map_map (measurable_splitFirstTwo _ _) (measurable_of_countable _)]
  congr 1
  funext bits
  rw [PlayerSpecificAlgebraicFourMergedDraw.draw,PlayerSpecificAlgebraicSplitFirstTwo.value _ _ _ _ hm hirr x hx.1,hp.1,hp.2.1]
  rfl

theorem CDF_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) :
    CDFClose (law model root a H K x) (i.smallUniformLaw hcase) (8/(2:ℝ)^H+1/(2*(2:ℝ)^K)) := by
  have hp := PlayerSpecificAlgebraicFourMergedInput.values model root a i hm hirr hv x hx ha T hfit hcase
  rw [law_eq model root a i hm hirr hv x hx ha T hfit hcase H K]
  exact splitLaw_CDFClose _ _ (PlayerSpecificThreeDrawLaw.CDF_error model root _
    (i.smallUniformInput hcase).childSpec H K hm hirr hv x hx hp.2.2)

end Blotto.PlayerSpecificFourMergedDrawLaw
