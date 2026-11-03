import Blotto.PlayerSpecificOrderedFourDrawLaw
import Blotto.PlayerSpecificAlgebraicFourSpecDraw

/-! The actual unsorted four-variable draw retains and restores its
three-comparison permutation. Its complete local bound holds in the
original coordinate order, including ties and the last mixture coordinate. -/
namespace Blotto.PlayerSpecificFourSpecDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicFourSpecInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 4 :=
  (fairBitLaw ((80*H+K)+K)).map (fun bits => values (PlayerSpecificAlgebraicFourSpecDraw.draw r a H K bits) x)

theorem law_eq (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourSpec)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x) (H K : ℕ) :
    law r a H K x=permuteLaw (permutationWithLast (sortTriplePermutation i.length)).symm
      (PlayerSpecificOrderedFourDrawLaw.law r (prepare RationalCostModel.schoolbook r.root a).input H K x) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits => values (PlayerSpecificAlgebraicFourSpecDraw.draw r a H K bits) x) _=
    Measure.map (permuteAllocation (permutationWithLast (sortTriplePermutation i.length)).symm)
      (Measure.map (fun bits => values (PlayerSpecificAlgebraicOrderedFourDraw.draw r
        (prepare RationalCostModel.schoolbook r.root a).input H K bits) x)
          (fairBitLaw ((80*H+K)+K) : Measure (Fin ((80*H+K)+K) → Bool)))
  rw [Measure.map_map (measurable_permuteAllocation _) (measurable_of_countable _)]
  congr 1
  funext bits
  rw [PlayerSpecificAlgebraicFourSpecDraw.draw,PlayerSpecificAlgebraicPermutation.value,
    PlayerSpecificAlgebraicFourSpecDraw.permutation_value r a i hm hirr hv x hx ha]
  rfl

theorem CDF_error (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourSpec)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) (H K : ℕ) :
    CDFClose (law r a H K x) i.law (80/(2:ℝ)^H+3/(2*(2:ℝ)^K)) := by
  have hp := PlayerSpecificAlgebraicFourSpecInput.values RationalCostModel.schoolbook r.root a i hm hirr hv x hx ha
  have hf := fits RationalCostModel.schoolbook r.root a T hfit
  rw [law_eq r a i hm hirr hv x hx ha H K]
  exact permuteLaw_CDFClose (PlayerSpecificOrderedFourDrawLaw.CDF_error r _ i.input hm hirr hv x hx hp.1 T hf hml hmT hT H K) _

end Blotto.PlayerSpecificFourSpecDrawLaw
