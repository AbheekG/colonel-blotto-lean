import Blotto.PlayerSpecificFourSmallHybrid

/-! The ordered dispatcher has one H-independent finite-midpoint
exact-choice hybrid in both its normal and small branches. -/
namespace Blotto.PlayerSpecificOrderedFourHybrid
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem exists_hybrid (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) (K : ℕ) :
    ∃ hybrid : Mixed 4,
      (∀ H,PlayerSpecificEventDistance.Bound (PlayerSpecificOrderedFourDrawLaw.law r a H K x) hybrid (80/(2:ℝ)^H)) ∧
      CDFClose hybrid i.law (3/(2*(2:ℝ)^K)) := by
  have hc := PlayerSpecificAlgebraicOrderedFourDraw.normal_correct r a i hm hirr hv x hx ha
  by_cases hcase : (1-i.p)*i.ell ≤ i.w
  · refine ⟨(i.gluingDescriptor hcase).dyadicLaw K,?_,?_⟩
    · intro H
      rw [PlayerSpecificOrderedFourDrawLaw.normal_law r a H K x (hc.mpr hcase)]
      exact fun A hA => PlayerSpecificFourGluingDrawLaw.event_error RationalCostModel.schoolbook r.root a i H K hm hirr hv x hx ha
        T hfit hml hmT hT hcase A hA
    · have h := (i.gluingDescriptor hcase).dyadicLaw_CDF_error K
      have he : (i.gluingDescriptor hcase).law=i.gluingCaseLaw hcase := ProbabilityMeasure.toMeasure_injective (i.gluingDescriptor_law hcase)
      rw [he] at h
      rw [FourInput.law,dite_eq_left hcase]
      exact h.mono (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  · obtain ⟨hybrid,hevent,hCDF⟩ := PlayerSpecificFourSmallHybrid.exists_hybrid r a i hm hirr hv x hx ha T hfit hml hmT hT (lt_of_not_ge hcase) K
    refine ⟨hybrid,?_,?_⟩
    · intro H
      rw [PlayerSpecificOrderedFourDrawLaw.small_law r a H K x (fun h => hcase (hc.mp h))]
      exact PlayerSpecificEventDistance.mono _ _ _ _ (hevent H) (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    · rw [FourInput.law,dite_eq_right hcase]
      exact hCDF

end Blotto.PlayerSpecificOrderedFourHybrid
