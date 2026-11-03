import Blotto.PlayerSpecificFourSmallDrawLaw
import Blotto.PlayerSpecificFourGluingDrawLaw

/-! The actual ordered four-variable guard selects a complete branch
with a fixed reserved packet. Unused suffix bits preserve each branch law. -/
namespace Blotto.PlayerSpecificOrderedFourDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 4 :=
  (fairBitLaw ((80*H+K)+K)).map (fun bits => values (PlayerSpecificAlgebraicOrderedFourDraw.draw r a H K bits) x)

theorem normal_law (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (hn : PlayerSpecificAlgebraicOrderedFourDraw.normal r a=true) :
    law r a H K x=PlayerSpecificFourGluingDrawLaw.law RationalCostModel.schoolbook r.root a H K x := by
  have hb : 80*H+K ≤ (80*H+K)+K := by omega
  have he : (fun bits => values (PlayerSpecificAlgebraicOrderedFourDraw.draw r a H K bits) x)=
      (fun bits => values (PlayerSpecificAlgebraicFourGluingDraw.draw RationalCostModel.schoolbook r.root a H K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits hb bits)) x) := by
    funext bits
    rw [PlayerSpecificAlgebraicOrderedFourDraw.draw,ite_eq_left hn]
    rfl
  unfold law
  rw [he,PlayerSpecificFairPrefix.law (80*H+K) _ hb
    (fun bits => values (PlayerSpecificAlgebraicFourGluingDraw.draw RationalCostModel.schoolbook r.root a H K bits) x)]
  rfl

theorem small_law (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (hn : PlayerSpecificAlgebraicOrderedFourDraw.normal r a≠true) :
    law r a H K x=PlayerSpecificFourSmallDrawLaw.law r a H K x := by
  have he : (fun bits => values (PlayerSpecificAlgebraicOrderedFourDraw.draw r a H K bits) x)=
      (fun bits => values (PlayerSpecificAlgebraicFourSmallDraw.draw r a H K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (PlayerSpecificAlgebraicOrderedFourDraw.small_bit_bound H K) bits)) x) := by
    funext bits
    rw [PlayerSpecificAlgebraicOrderedFourDraw.draw,ite_eq_right hn]
  unfold law
  rw [he,PlayerSpecificFairPrefix.law _ _ (PlayerSpecificAlgebraicOrderedFourDraw.small_bit_bound H K)
    (fun bits => values (PlayerSpecificAlgebraicFourSmallDraw.draw r a H K bits) x)]
  rfl

theorem CDF_error (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) (H K : ℕ) :
    CDFClose (law r a H K x) i.law (80/(2:ℝ)^H+3/(2*(2:ℝ)^K)) := by
  have hc := PlayerSpecificAlgebraicOrderedFourDraw.normal_correct r a i hm hirr hv x hx ha
  have hmid : 1/(2*(2:ℝ)^K) ≤ 3/(2*(2:ℝ)^K) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hchoice : 20/(2:ℝ)^H ≤ 80/(2:ℝ)^H := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  by_cases hcase : (1-i.p)*i.ell ≤ i.w
  · rw [normal_law r a H K x (hc.mpr hcase),FourInput.law,dite_eq_left hcase]
    exact (PlayerSpecificFourGluingDrawLaw.CDF_error RationalCostModel.schoolbook r.root a i H K hm hirr hv x hx ha
      T hfit hml hmT hT hcase).mono (add_le_add le_rfl hmid)
  · rw [small_law r a H K x (fun h => hcase (hc.mp h)),FourInput.law,dite_eq_right hcase]
    exact (PlayerSpecificFourSmallDrawLaw.CDF_error r a i hm hirr hv x hx ha T hfit hml hmT hT (lt_of_not_ge hcase) H K).mono
      (add_le_add hchoice le_rfl)

end Blotto.PlayerSpecificOrderedFourDrawLaw
