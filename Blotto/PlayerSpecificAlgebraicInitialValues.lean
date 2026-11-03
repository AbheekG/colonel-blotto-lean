import Blotto.PlayerSpecificAlgebraicInitial

/-! Every actual initial length and mean-mixture row evaluates to the
paper's player-specific marginal formula at the retained real root. -/
namespace Blotto.PlayerSpecificAlgebraicInitialValues
open SignType PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicInitial
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem components (model : RationalCostModel) (candidate : Candidate) (v w : ℚ)
    (hm : Normalized candidate.polynomial) (hirr : Irreducible (semantics candidate.polynomial))
    (hnode : candidate.interval.lo<candidate.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique candidate.polynomial candidate.interval x)
    (hv : (0:ℝ)<(v:ℝ)) (hw : (0:ℝ)<(w:ℝ)) (hg : 0<x) :
    realEvaluate (numerator model candidate v w) x=min (v:ℝ) (x*(w:ℝ)) ∧
      realEvaluate (probabilityA model candidate v w) x=PlayerSpecificMarginals.probA (v:ℝ) (w:ℝ) x ∧
      realEvaluate (probabilityB model candidate v w) x=PlayerSpecificMarginals.probB (v:ℝ) (w:ℝ) x := by
  have hm0 : candidate.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hc:=PlayerSpecificAlgebraicField.constant_value candidate.polynomial v x hx.1
  have hgw:=weighted_value candidate w x hx.1
  have hone:=PlayerSpecificAlgebraicField.constant_value candidate.polynomial 1 x hx.1
  have hdivA:=PlayerSpecificAlgebraicField.divide_value candidate.polynomial
    (PlayerSpecificAlgebraicField.constant candidate.polynomial v) (weighted candidate w) hm hirr
    (weighted_reduced candidate w hm hm0) x hx.1
  have hdivB:=PlayerSpecificAlgebraicField.divide_value candidate.polynomial
    (weighted candidate w) (PlayerSpecificAlgebraicField.constant candidate.polynomial v) hm hirr
    (PlayerSpecificAlgebraicField.constant_reduced candidate.polynomial v hm hm0) x hx.1
  rw [hc,hgw] at hdivA hdivB
  have htest:=low_correct model candidate v w hm hirr hnode x hx
  by_cases h : (v:ℝ)≤x*(w:ℝ)
  · have hl:=htest.mpr h
    have hf:=PlayerSpecificMarginals.low_formulas hv hw hg h (1:ℝ)
    simp only [numerator,probabilityA,probabilityB,hl,ite_true]
    exact ⟨hc.trans (min_eq_left h).symm,hdivA.trans hf.2.1.symm,hone.trans (by simpa only [Rat.cast_one] using hf.2.2.symm)⟩
  · have hl : low model candidate v w≠true := by intro he; exact h (htest.mp he)
    have hh : x*(w:ℝ)≤(v:ℝ) := (lt_of_not_ge h).le
    have hf:=PlayerSpecificMarginals.high_formulas hv hw hg hh (1:ℝ)
    simp only [numerator,probabilityA,probabilityB,hl]
    exact ⟨hgw.trans (min_eq_right hh).symm,hone.trans (by simpa only [Rat.cast_one] using hf.2.1.symm),hdivB.trans hf.2.2.symm⟩

theorem actual_values (model : RationalCostModel) (candidate : Candidate) (inverseScale : Data) (v w : ℚ)
    (hm : Normalized candidate.polynomial) (hirr : Irreducible (semantics candidate.polynomial))
    (hnode : candidate.interval.lo<candidate.interval.hi) (x scale : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique candidate.polynomial candidate.interval x)
    (hv : (0:ℝ)<(v:ℝ)) (hw : (0:ℝ)<(w:ℝ)) (hg : 0<x)
    (hinv : realEvaluate inverseScale x=scale⁻¹) :
    realEvaluate (run model candidate inverseScale v w).length x=PlayerSpecificMarginals.length (v:ℝ) (w:ℝ) x scale ∧
      realEvaluate (run model candidate inverseScale v w).initialA x=
        PlayerSpecificMarginals.probA (v:ℝ) (w:ℝ) x*PlayerSpecificMarginals.length (v:ℝ) (w:ℝ) x scale ∧
      realEvaluate (run model candidate inverseScale v w).initialB x=
        PlayerSpecificMarginals.probB (v:ℝ) (w:ℝ) x*PlayerSpecificMarginals.length (v:ℝ) (w:ℝ) x scale := by
  have hc:=components model candidate v w hm hirr hnode x hx hv hw hg
  have hl : realEvaluate (run model candidate inverseScale v w).length x=PlayerSpecificMarginals.length (v:ℝ) (w:ℝ) x scale := by
    rw [run_length,PlayerSpecificAlgebraicField.times_value candidate.polynomial _ _ x hx.1,hc.1,hinv]
    rfl
  refine ⟨hl,?_,?_⟩
  · rw [run_initialA,PlayerSpecificAlgebraicField.times_value candidate.polynomial _ _ x hx.1,hc.2.1,hl]
  · rw [run_initialB,PlayerSpecificAlgebraicField.times_value candidate.polynomial _ _ x hx.1,hc.2.2,hl]

end Blotto.PlayerSpecificAlgebraicInitialValues
