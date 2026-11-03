import Blotto.PlayerSpecificAlgebraicExpression

/-! The executing algebraic expression has exactly the previously
checked real expression value at the retained root, including total
division, min/max and selected-only conditionals. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionValue
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicExpression
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem value {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j)) :
    realEvaluate (run model root env e) x=e.realValue (realEnv env x) := by
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  induction e with
  | input j => simp only [run,RationalExpression.realValue_input,realEnv,FixedArrayTable.read_ofFn]
  | literal q => exact PlayerSpecificAlgebraicField.constant_value _ _ x hx.1
  | add a b ha hb =>
      simp only [run,PlayerSpecificAlgebraicField.plus_value _ _ _ x hx.1,ha,hb,RationalExpression.realValue_add]
  | sub a b ha hb =>
      simp only [run,PlayerSpecificAlgebraicField.minus_value _ _ _ x hx.1,ha,hb,RationalExpression.realValue_sub]
  | mul a b ha hb =>
      simp only [run,PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,ha,hb,RationalExpression.realValue_mul]
  | div a b ha hb =>
      simp only [run,PlayerSpecificAlgebraicField.divide_value _ _ _ hm hirr
        (PlayerSpecificAlgebraicExpression.reduced model root env b hm hm0 hEnv) x hx.1,ha,hb,RationalExpression.realValue_div]
  | minimum a b ha hb =>
      have hc:=PlayerSpecificAlgebraicPairStep.le_correct model root (run model root env a) (run model root env b) hm hirr hv x hx
      rw [ha,hb] at hc
      by_cases hfit : PlayerSpecificAlgebraicPairStep.le model root (run model root env a) (run model root env b)=true
      · simp only [run,ite_eq_left hfit,ha,RationalExpression.realValue_minimum,min_eq_left (hc.mp hfit)]
      · have hgt:=lt_of_not_ge (fun h => hfit (hc.mpr h))
        simp only [run,ite_eq_right hfit,hb,RationalExpression.realValue_minimum,min_eq_right hgt.le]
  | maximum a b ha hb =>
      have hc:=PlayerSpecificAlgebraicPairStep.le_correct model root (run model root env a) (run model root env b) hm hirr hv x hx
      rw [ha,hb] at hc
      by_cases hfit : PlayerSpecificAlgebraicPairStep.le model root (run model root env a) (run model root env b)=true
      · simp only [run,ite_eq_left hfit,hb,RationalExpression.realValue_maximum,max_eq_right (hc.mp hfit)]
      · have hgt:=lt_of_not_ge (fun h => hfit (hc.mpr h))
        simp only [run,ite_eq_right hfit,ha,RationalExpression.realValue_maximum,max_eq_left hgt.le]
  | ifLe a b yes no ha hb hy hn =>
      have hc:=PlayerSpecificAlgebraicPairStep.le_correct model root (run model root env a) (run model root env b) hm hirr hv x hx
      rw [ha,hb] at hc
      by_cases hfit : PlayerSpecificAlgebraicPairStep.le model root (run model root env a) (run model root env b)=true
      · simp only [run,ite_eq_left hfit,hy,RationalExpression.realValue_ifLe,ite_eq_left (hc.mp hfit)]
      · simp only [run,ite_eq_right hfit,hn,RationalExpression.realValue_ifLe,ite_eq_right (fun h => hfit (hc.mpr h))]

end Blotto.PlayerSpecificAlgebraicExpressionValue
