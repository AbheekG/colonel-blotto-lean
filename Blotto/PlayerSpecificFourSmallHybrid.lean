import Blotto.PlayerSpecificFourReflectedHybrid

/-! One fixed finite-midpoint hybrid covers the complete actual small
branch, including its outer coin and both complete continuations. -/
namespace Blotto.PlayerSpecificFourSmallHybrid
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem exists_hybrid (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (K : ℕ) :
    ∃ hybrid : Mixed 4,
      (∀ H,PlayerSpecificEventDistance.Bound (PlayerSpecificFourSmallDrawLaw.law r a H K x) hybrid (20/(2:ℝ)^H)) ∧
      CDFClose hybrid (i.smallCaseLaw hcase) (3/(2*(2:ℝ)^K)) := by
  obtain ⟨reflected,href,hCDF⟩ := PlayerSpecificFourReflectedHybrid.exists_hybrid r a i hm hirr hv x hx ha T hfit hml hmT hT hcase K
  let u := i.smallUniformDyadicLaw hcase K
  have hp : 0 ≤ i.p ∧ i.p ≤ 1 := ⟨i.p_pos.le,i.p_lt.le⟩
  refine ⟨binaryLaw i.p hp u reflected,?_,?_⟩
  · intro H
    have hu : PlayerSpecificEventDistance.Bound
        ((fairBitLaw (PlayerSpecificAlgebraicFourSmallDraw.remaining H K)).map (PlayerSpecificFourSmallDrawLaw.upper r a H K x))
        u (19/(2:ℝ)^H) := by
      unfold PlayerSpecificFourSmallDrawLaw.upper
      rw [PlayerSpecificFairPrefix.law (8*H+K) _ (PlayerSpecificAlgebraicFourSmallDraw.uniform_bit_bound H K)
        (fun bits => values (PlayerSpecificAlgebraicFourMergedDraw.draw RationalCostModel.schoolbook r.root a H K bits) x)]
      exact PlayerSpecificEventDistance.mono _ _ _ _
        (PlayerSpecificFourMergedHybrid.event_bound r a i hm hirr hv x hx ha T hfit hcase H K)
        (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    have hl : PlayerSpecificEventDistance.Bound
        ((fairBitLaw (PlayerSpecificAlgebraicFourSmallDraw.remaining H K)).map (PlayerSpecificFourSmallDrawLaw.lower r a H K x))
        reflected (19/(2:ℝ)^H) := href H
    have hprob : 0 ≤ realEvaluate a.probability x ∧ realEvaluate a.probability x ≤ 1 := by rw [ha.probability]; exact hp
    have h := PlayerSpecificBinaryEventTransfer.actual_choice RationalCostModel.schoolbook r.root a.probability H
      (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) (PlayerSpecificFourSmallDrawLaw.upper r a H K x)
        (PlayerSpecificFourSmallDrawLaw.lower r a H K x) hm hirr hv x hx hprob u reflected _ hu hl
    have he : 1/(2:ℝ)^H+19/(2:ℝ)^H=20/(2:ℝ)^H := by ring
    rw [he] at h
    rw [PlayerSpecificFourSmallDrawLaw.law_eq]
    simpa only [ha.probability] using h
  · exact binaryLaw_CDFClose i.p hp (i.smallUniformDyadicLaw_CDF_error hcase K) hCDF

end Blotto.PlayerSpecificFourSmallHybrid
