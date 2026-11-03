import Blotto.PlayerSpecificMinimumPolynomialCost

/-! Short remainders do not introduce fresh leading-coefficient
denominators. The statement identifies the actual executing division
return, rather than replacing it by a different arithmetic algorithm. -/
namespace Blotto.PlayerSpecificShortReduction
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem normalized_injective (a b : Data) (ha : Normalized a) (hb : Normalized b)
    (he : semantics a=semantics b) : a=b := by
  by_cases ha0 : a=[]
  · subst a
    have hb0 : semantics b=0 := he.symm
    by_contra hn
    exact (nonzero b hb (Ne.symm hn)) hb0
  by_cases hb0 : b=[]
  · subst b
    exact False.elim ((nonzero a ha ha0) he)
  have hlen : a.length=b.length := by
    have h:=congrArg Polynomial.natDegree he
    rw [degree_eq a ha ha0,degree_eq b hb hb0] at h
    have hap:=List.length_pos_iff.mpr ha0
    have hbp:=List.length_pos_iff.mpr hb0
    omega
  apply List.ext_getElem hlen
  intro j hja hjb
  have hc:=congrArg (fun p : Polynomial ℚ => p.coeff j) he
  simpa only [coefficient,List.getElem?_eq_getElem hja,List.getElem?_eq_getElem hjb,Option.getD_some] using hc

theorem short_degree (m a : Data) (hm : Normalized m) (hm0 : m≠[]) (hl : a.length<m.length) :
    (semantics a).degree<(semantics m).degree := by
  by_cases ha0 : semantics a=0
  · rw [ha0,Polynomial.degree_zero,Polynomial.degree_eq_natDegree (nonzero m hm hm0)]
    exact WithBot.bot_lt_coe _
  · rw [Polynomial.degree_eq_natDegree ha0,Polynomial.degree_eq_natDegree (nonzero m hm hm0),Nat.cast_lt,
      degree_eq m hm hm0]
    have hp:=degree_le a
    have ha : a≠[] := by intro hz; exact ha0 (by rw [hz]; rfl)
    have hpos:=List.length_pos_iff.mpr ha
    omega

theorem reduce_eq_trim (m a : Data) (hm : Normalized m) (hm0 : m≠[]) (hl : a.length<m.length) :
    reduce m a=trim a := by
  have hd:=short_degree m a hm hm0 hl
  have he:=((PlayerSpecificPolynomialDivision.refines a m).2).symm
  rw [(Polynomial.mod_eq_self_iff (nonzero m hm hm0)).mpr hd] at he
  apply normalized_injective _ _ (reduced m a hm hm0).1 (trim_normalized a)
  exact he.trans (trim_semantics a).symm

theorem reduce_height (m a : Data) (hm : Normalized m) (hm0 : m≠[]) (hl : a.length<m.length)
    (H : ℕ) (ha : HasHeight a H) : HasHeight (reduce m a) H := by
  rw [reduce_eq_trim m a hm hm0 hl]
  exact trim_height ha

theorem plus_height (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) (hb : Reduced m b)
    (S T : ℕ) (haH : HasHeight a S) (hbH : HasHeight b T) :
    HasHeight (PlayerSpecificAlgebraicField.plus m a b) (S+T+1) := by
  exact reduce_height m (add a b) hm hm0 (by rw [add_length]; have hl:=ha.2; have hl':=hb.2; omega) _
    (add_height haH hbH)

theorem minus_height (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) (hb : Reduced m b)
    (S T : ℕ) (haH : HasHeight a S) (hbH : HasHeight b T) :
    HasHeight (PlayerSpecificAlgebraicField.minus m a b) (S+T+1) := by
  exact reduce_height m (subtract a b) hm hm0 (by
    rw [subtract,add_length,scale_length]; have hl:=ha.2; have hl':=hb.2; omega) _ (subtract_height haH hbH)

end Blotto.PlayerSpecificShortReduction
