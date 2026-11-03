import Blotto.PlayerSpecificAlgebraicZero

/-! Executable field operations in the retained real embedding. Every
returned coefficient row is reduced; inverse certificates are reduced by
modular Horner, so no long raw certificate enters a capped division. -/
namespace Blotto.PlayerSpecificAlgebraicField
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

def constant (m : Data) (q : ℚ) : Data := reduce m [q]
def plus (m a b : Data) : Data := reduce m (add a b)
def minus (m a b : Data) : Data := reduce m (subtract a b)
def negative (m a : Data) : Data := reduce m (scale (-1) a)
def times (m a b : Data) : Data := PlayerSpecificModularHorner.run m b a
def inverse (m a : Data) : Data :=
  if a=[] then [] else PlayerSpecificModularHorner.reduceLong m (PlayerSpecificAlgebraicBezout.right m a)
def divide (m a b : Data) : Data := times m a (inverse m b)
def equal (m a b : Data) : Bool := PlayerSpecificAlgebraicZero.run (minus m a b)

theorem constant_reduced (m : Data) (q : ℚ) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (constant m q) :=
  reduced m [q] hm hm0
theorem plus_reduced (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (plus m a b) :=
  reduced m _ hm hm0
theorem minus_reduced (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (minus m a b) :=
  reduced m _ hm hm0
theorem negative_reduced (m a : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (negative m a) :=
  reduced m _ hm hm0
theorem times_reduced (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (times m a b) :=
  PlayerSpecificModularHorner.reduced m b a hm hm0
theorem inverse_reduced (m a : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (inverse m a) := by
  rw [inverse]
  split
  · exact nil_reduced m hm0
  · exact PlayerSpecificModularHorner.reduced m [1] _ hm hm0
theorem divide_reduced (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (divide m a b) :=
  times_reduced m a _ hm hm0

theorem constant_value (m : Data) (q : ℚ) (x : ℝ) (hx : realEvaluate m x=0) : realEvaluate (constant m q) x=(q:ℝ) := by
  rw [constant,real_reduce m _ x hx]
  simp only [realEvaluate,List.foldr_cons,List.foldr_nil,mul_zero,add_zero]
theorem plus_value (m a b : Data) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (plus m a b) x=realEvaluate a x+realEvaluate b x := by
  rw [plus,real_reduce m _ x hx,real_add]
theorem minus_value (m a b : Data) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (minus m a b) x=realEvaluate a x-realEvaluate b x := by
  rw [minus,real_reduce m _ x hx,real_subtract]
theorem negative_value (m a : Data) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (negative m a) x= -realEvaluate a x := by
  rw [negative,real_reduce m _ x hx,real_scale]
  simp only [Rat.cast_neg,Rat.cast_one,neg_one_mul]
theorem times_value (m a b : Data) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (times m a b) x=realEvaluate a x*realEvaluate b x :=
  PlayerSpecificModularHorner.real_value m b a x hx

theorem inverse_value (m a : Data) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (ha : Reduced m a) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (inverse m a) x=(realEvaluate a x)⁻¹ := by
  rw [inverse]
  split
  · rename_i hz
    subst a
    simp only [realEvaluate,List.foldr_nil,inv_zero]
  · rename_i hne
    have hm0 : m≠[] := by intro h; exact hirr.ne_zero (by rw [h]; rfl)
    have ha0:=nonzero a ha.1 hne
    have hd:=degree_lt m a hm hm0 ha ha0
    have hi:=PlayerSpecificAlgebraicBezout.real_identity m a hirr ha0 hd x hx
    have hn:=PlayerSpecificAlgebraicZero.real_nonzero m a hm hirr ha hne x hx
    rw [PlayerSpecificModularHorner.reduceLong_value m _ x hx]
    apply mul_left_cancel₀ hn
    rw [mul_inv_cancel₀ hn]
    exact hi

theorem divide_value (m a b : Data) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (hb : Reduced m b) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (divide m a b) x=realEvaluate a x/realEvaluate b x := by
  rw [divide,times_value m a _ x hx,inverse_value m b hm hirr hb x hx,div_eq_mul_inv]

theorem equal_value (m a b : Data) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (x : ℝ) (hx : realEvaluate m x=0) : equal m a b=true ↔ realEvaluate a x=realEvaluate b x := by
  have hm0 : m≠[] := by intro h; exact hirr.ne_zero (by rw [h]; rfl)
  rw [equal,PlayerSpecificAlgebraicZero.actual_contract m _ hm hirr (minus_reduced m a b hm hm0) x hx,
    minus_value m a b x hx,sub_eq_zero]

end Blotto.PlayerSpecificAlgebraicField
