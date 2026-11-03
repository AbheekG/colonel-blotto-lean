import Blotto.PlayerSpecificShortReduction

/-! Exact coefficient-level addition/subtraction identities for reduced
rows. No evaluation at a selected root or equality oracle is needed. -/
namespace Blotto.PlayerSpecificAdditiveFieldSemantics
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificShortReduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem plus (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) (hb : Reduced m b) :
    semantics (PlayerSpecificAlgebraicField.plus m a b)=semantics a+semantics b := by
  rw [PlayerSpecificAlgebraicField.plus,reduce_eq_trim m (add a b) hm hm0 (by
    rw [add_length]; have h:=ha.2; have h':=hb.2; omega),trim_semantics,add_semantics]

theorem minus (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) (hb : Reduced m b) :
    semantics (PlayerSpecificAlgebraicField.minus m a b)=semantics a-semantics b := by
  rw [PlayerSpecificAlgebraicField.minus,reduce_eq_trim m (subtract a b) hm hm0 (by
    rw [subtract,add_length,scale_length]; have h:=ha.2; have h':=hb.2; omega),trim_semantics,subtract_semantics]

theorem negative (m a : Data) (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) :
    semantics (PlayerSpecificAlgebraicField.negative m a)= -semantics a := by
  rw [PlayerSpecificAlgebraicField.negative,reduce_eq_trim m (scale (-1) a) hm hm0 (by rw [scale_length]; exact ha.2),
    trim_semantics,scale_semantics]
  simp only [map_neg,map_one,neg_one_mul]

theorem negative_height (m a : Data) (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a)
    (H : ℕ) (haH : HasHeight a H) : HasHeight (PlayerSpecificAlgebraicField.negative m a) H :=
  reduce_height m (scale (-1) a) hm hm0 (by rw [scale_length]; exact ha.2) H
    (PlayerSpecificPolynomialHeights.negative_height haH)

theorem plus_assoc (m a b c : Data) (hm : Normalized m) (hm0 : m≠[])
    (ha : Reduced m a) (hb : Reduced m b) (hc : Reduced m c) :
    PlayerSpecificAlgebraicField.plus m (PlayerSpecificAlgebraicField.plus m a b) c=
      PlayerSpecificAlgebraicField.plus m a (PlayerSpecificAlgebraicField.plus m b c) := by
  apply normalized_injective _ _ (PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0).1
    (PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0).1
  rw [plus m _ _ hm hm0 (PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0) hc,
    plus m _ _ hm hm0 ha (PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0),
    plus m a b hm hm0 ha hb,plus m b c hm hm0 hb hc,add_assoc]

end Blotto.PlayerSpecificAdditiveFieldSemantics
