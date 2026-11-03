import Blotto.PlayerSpecificAlgebraicPairStep

/-! The actual retained-root pair routine refines the paper's rounding
endpoints and exact lottery probability, including equality branches. -/
namespace Blotto.PlayerSpecificAlgebraicPairValues
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicPairStep
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem total (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (x : ℝ) (hx : realEvaluate root.polynomial x=0) :
    realEvaluate (run model root lengthA lengthB a b).total x=realEvaluate a x+realEvaluate b x :=
  PlayerSpecificAlgebraicField.plus_value _ _ _ _ hx

theorem upper (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ) (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    realEvaluate (run model root lengthA lengthB a b).upperA x=
      min (realEvaluate lengthA x) (realEvaluate a x+realEvaluate b x) := by
  let t:=PlayerSpecificAlgebraicField.plus root.polynomial a b
  have ht : realEvaluate t x=realEvaluate a x+realEvaluate b x := PlayerSpecificAlgebraicField.plus_value _ _ _ _ hx.1
  have hc:=le_correct model root t lengthA hm hirr hv x hx
  change realEvaluate (if le model root t lengthA then t else lengthA) x=_
  by_cases h : le model root t lengthA=true
  · rw [ite_eq_left h,ht,min_eq_right (by rw [←ht]; exact hc.mp h)]
  · rw [ite_eq_right h,min_eq_left (by have hn:=mt hc.mpr h; rw [ht] at hn; exact (lt_of_not_ge hn).le)]

theorem lower (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ) (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    realEvaluate (run model root lengthA lengthB a b).lowerA x=
      max 0 (realEvaluate a x+realEvaluate b x-realEvaluate lengthB x) := by
  let t:=PlayerSpecificAlgebraicField.plus root.polynomial a b
  have ht : realEvaluate t x=realEvaluate a x+realEvaluate b x := PlayerSpecificAlgebraicField.plus_value _ _ _ _ hx.1
  have hc:=le_correct model root t lengthB hm hirr hv x hx
  change realEvaluate (if le model root t lengthB then [] else PlayerSpecificAlgebraicField.minus root.polynomial t lengthB) x=_
  by_cases h : le model root t lengthB=true
  · rw [ite_eq_left h,max_eq_left (by have hh:=hc.mp h; rw [ht] at hh; linarith)]
    rfl
  · rw [ite_eq_right h,PlayerSpecificAlgebraicField.minus_value _ _ _ _ hx.1,ht,
      max_eq_right (by have hn:=mt hc.mpr h; rw [ht] at hn; linarith)]

theorem upper_other (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (x : ℝ) (hx : realEvaluate root.polynomial x=0) :
    realEvaluate (run model root lengthA lengthB a b).upperB x=
      realEvaluate a x+realEvaluate b x-realEvaluate (run model root lengthA lengthB a b).upperA x := by
  have ht:=PlayerSpecificAlgebraicField.plus_value root.polynomial a b x hx
  change realEvaluate (if le model root (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthA then [] else
      PlayerSpecificAlgebraicField.minus root.polynomial (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthA) x=
    realEvaluate a x+realEvaluate b x-realEvaluate (if le model root (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthA then
      PlayerSpecificAlgebraicField.plus root.polynomial a b else lengthA) x
  split
  · change (0:ℝ)=realEvaluate a x+realEvaluate b x-realEvaluate (PlayerSpecificAlgebraicField.plus root.polynomial a b) x
    rw [ht,sub_self]
  · rw [PlayerSpecificAlgebraicField.minus_value _ _ _ _ hx,ht]

theorem lower_other (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (x : ℝ) (hx : realEvaluate root.polynomial x=0) :
    realEvaluate (run model root lengthA lengthB a b).lowerB x=
      realEvaluate a x+realEvaluate b x-realEvaluate (run model root lengthA lengthB a b).lowerA x := by
  have ht:=PlayerSpecificAlgebraicField.plus_value root.polynomial a b x hx
  change realEvaluate (if le model root (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthB then
      PlayerSpecificAlgebraicField.plus root.polynomial a b else lengthB) x=
    realEvaluate a x+realEvaluate b x-realEvaluate (if le model root (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthB then [] else
      PlayerSpecificAlgebraicField.minus root.polynomial (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthB) x
  split
  · change realEvaluate (PlayerSpecificAlgebraicField.plus root.polynomial a b) x=realEvaluate a x+realEvaluate b x-0
    rw [ht,sub_zero]
  · rw [PlayerSpecificAlgebraicField.minus_value _ _ _ _ hx,ht]; ring

theorem probability (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (x : ℝ) (hx : realEvaluate root.polynomial x=0) :
    realEvaluate (run model root lengthA lengthB a b).probability x=
      (realEvaluate a x-realEvaluate (run model root lengthA lengthB a b).lowerA x)/
      (realEvaluate (run model root lengthA lengthB a b).upperA x-realEvaluate (run model root lengthA lengthB a b).lowerA x) := by
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  change realEvaluate (PlayerSpecificAlgebraicField.divide root.polynomial
    (PlayerSpecificAlgebraicField.minus root.polynomial a (run model root lengthA lengthB a b).lowerA)
    (PlayerSpecificAlgebraicField.minus root.polynomial (run model root lengthA lengthB a b).upperA (run model root lengthA lengthB a b).lowerA)) x=_
  rw [PlayerSpecificAlgebraicField.divide_value _ _ _ hm hirr (PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0) x hx,
    PlayerSpecificAlgebraicField.minus_value _ _ _ _ hx,PlayerSpecificAlgebraicField.minus_value _ _ _ _ hx]

end Blotto.PlayerSpecificAlgebraicPairValues
