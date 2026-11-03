import Blotto.PlayerSpecificOrderedFourHybrid

/-! Exact native sorting/restoration preserves the whole-event bound
to an H-independent finite-midpoint hybrid in the original coordinates. -/
namespace Blotto.PlayerSpecificFourSpecHybrid
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicFourSpecInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem exists_hybrid (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourSpec)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourSpecInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) (K : ℕ) :
    ∃ hybrid : Mixed 4,
      (∀ H,PlayerSpecificEventDistance.Bound (PlayerSpecificFourSpecDrawLaw.law r a H K x) hybrid (80/(2:ℝ)^H)) ∧
      CDFClose hybrid i.law (3/(2*(2:ℝ)^K)) := by
  have hp := PlayerSpecificAlgebraicFourSpecInput.values RationalCostModel.schoolbook r.root a i hm hirr hv x hx ha
  have hf := fits RationalCostModel.schoolbook r.root a T hfit
  obtain ⟨hybrid,hevent,hCDF⟩ := PlayerSpecificOrderedFourHybrid.exists_hybrid r (prepare RationalCostModel.schoolbook r.root a).input
    i.input hm hirr hv x hx hp.1 T hf hml hmT hT K
  let permutation := (permutationWithLast (sortTriplePermutation i.length)).symm
  refine ⟨permuteLaw permutation hybrid,?_,?_⟩
  · intro H
    rw [PlayerSpecificFourSpecDrawLaw.law_eq r a i hm hirr hv x hx ha H K]
    exact PlayerSpecificEventDistance.map _ _ _ (hevent H) (permuteAllocation permutation) (measurable_permuteAllocation _)
  · exact permuteLaw_CDFClose hCDF permutation

end Blotto.PlayerSpecificFourSpecHybrid
