import Blotto.PlayerSpecificBinaryDrawLaw
import Blotto.PlayerSpecificFourMergedDrawLaw
import Blotto.PlayerSpecificFourReflectedDrawLaw
import Blotto.PlayerSpecificFairPrefix

/-! The actual small four-variable branch includes its outer algebraic
coin, the reserved uniform subpacket and complete reflected continuation. -/
namespace Blotto.PlayerSpecificFourSmallDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def upper (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) → Bool) : Allocation 4 :=
  values (PlayerSpecificAlgebraicFourMergedDraw.draw RationalCostModel.schoolbook r.root a H K
    (PlayerSpecificAlgebraicFourSmallDraw.takeBits (PlayerSpecificAlgebraicFourSmallDraw.uniform_bit_bound H K) bits)) x

noncomputable def lower (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (bits : Fin (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) → Bool) : Allocation 4 :=
  values (PlayerSpecificAlgebraicFourReflectedDraw.draw r a H K bits) x

noncomputable def law (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 4 :=
  (fairBitLaw (PlayerSpecificAlgebraicFourSmallDraw.bitCount H K)).map
    (fun bits => values (PlayerSpecificAlgebraicFourSmallDraw.draw r a H K bits) x)

theorem law_eq (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ) :
    law r a H K x=PlayerSpecificBinaryDrawLaw.law RationalCostModel.schoolbook r.root a.probability H
      (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) (upper r a H K x) (lower r a H K x) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits => values (PlayerSpecificAlgebraicFourSmallDraw.draw r a H K bits) x) _=
    Measure.map (fun bits => if PlayerSpecificAlgebraicMidpointCoin.run RationalCostModel.schoolbook r.root a.probability H
      (firstBitBlock H (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits)
        then upper r a H K x (secondBitBlock H (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits)
        else lower r a H K x (secondBitBlock H (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits)) _
  congr 1
  funext bits
  by_cases h : PlayerSpecificAlgebraicMidpointCoin.run RationalCostModel.schoolbook r.root a.probability H
    (firstBitBlock H (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) bits)=true
  · simp only [PlayerSpecificAlgebraicFourSmallDraw.draw,h,ite_true,upper]
  · simp only [PlayerSpecificAlgebraicFourSmallDraw.draw,h,Bool.false_eq_true,ite_false,lower]

theorem CDF_error (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) :
    CDFClose (law r a H K x) (i.smallCaseLaw hcase) (20/(2:ℝ)^H+3/(2*(2:ℝ)^K)) := by
  have hE : 8/(2:ℝ)^H+1/(2*(2:ℝ)^K) ≤ 19/(2:ℝ)^H+3/(2*(2:ℝ)^K) :=
    add_le_add (div_le_div_of_nonneg_right (by norm_num) (by positivity))
      (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  have hu : CDFClose ((fairBitLaw (PlayerSpecificAlgebraicFourSmallDraw.remaining H K)).map (upper r a H K x))
      (i.smallUniformLaw hcase) (19/(2:ℝ)^H+3/(2*(2:ℝ)^K)) := by
    unfold upper
    rw [PlayerSpecificFairPrefix.law (8*H+K) _ (PlayerSpecificAlgebraicFourSmallDraw.uniform_bit_bound H K)
      (fun bits => values (PlayerSpecificAlgebraicFourMergedDraw.draw RationalCostModel.schoolbook r.root a H K bits) x)]
    exact (PlayerSpecificFourMergedDrawLaw.CDF_error RationalCostModel.schoolbook r.root a i hm hirr hv x hx ha T hfit hcase H K).mono hE
  have hl : CDFClose ((fairBitLaw (PlayerSpecificAlgebraicFourSmallDraw.remaining H K)).map (lower r a H K x))
      (i.reflectedZeroLaw hcase) (19/(2:ℝ)^H+3/(2*(2:ℝ)^K)) :=
    PlayerSpecificFourReflectedDrawLaw.CDF_error r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H K
  have hp : 0 ≤ realEvaluate a.probability x ∧ realEvaluate a.probability x ≤ 1 := by
    rw [ha.probability]
    exact ⟨i.p_pos.le,i.p_lt.le⟩
  have h := PlayerSpecificBinaryDrawLaw.CDF_error RationalCostModel.schoolbook r.root a.probability H
    (PlayerSpecificAlgebraicFourSmallDraw.remaining H K) (upper r a H K x) (lower r a H K x)
    hm hirr hv x hx hp (i.smallUniformLaw hcase) (i.reflectedZeroLaw hcase) _ hu hl
  have he : 1/(2:ℝ)^H+(19/(2:ℝ)^H+3/(2*(2:ℝ)^K))=20/(2:ℝ)^H+3/(2*(2:ℝ)^K) := by ring
  rw [he] at h
  rw [law_eq]
  simpa only [ha.probability,FourInput.smallCaseLaw] using h

end Blotto.PlayerSpecificFourSmallDrawLaw
