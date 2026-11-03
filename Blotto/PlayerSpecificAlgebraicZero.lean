import Blotto.PlayerSpecificAlgebraicBezout

/-! Coefficientwise zero is exact at the selected root for reduced elements.
This relies on the computed unit identity, not on numerical approximation. -/
namespace Blotto.PlayerSpecificAlgebraicZero
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run (a : Data) : Bool := decide (a=[])

theorem real_nonzero (m a : Data) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (ha : Reduced m a) (ha0 : a≠[]) (x : ℝ) (hx : realEvaluate m x=0) : realEvaluate a x≠0 := by
  have hm0 : m≠[] := by intro h; exact hirr.ne_zero (by rw [h]; rfl)
  have ha' := nonzero a ha.1 ha0
  have hdeg:=degree_lt m a hm hm0 ha ha'
  have hi:=PlayerSpecificAlgebraicBezout.real_identity m a hirr ha' hdeg x hx
  intro hz
  rw [hz,zero_mul] at hi
  exact zero_ne_one hi

theorem zero_iff (m a : Data) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (ha : Reduced m a) (x : ℝ) (hx : realEvaluate m x=0) : realEvaluate a x=0 ↔ a=[] := by
  constructor
  · intro hz
    by_contra hne
    exact real_nonzero m a hm hirr ha hne x hx hz
  · intro hz
    subst a
    rfl

theorem actual_contract (m a : Data) (hm : Normalized m) (hirr : Irreducible (semantics m))
    (ha : Reduced m a) (x : ℝ) (hx : realEvaluate m x=0) : run a=true ↔ realEvaluate a x=0 := by
  rw [run,decide_eq_true_eq,zero_iff m a hm hirr ha x hx]

end Blotto.PlayerSpecificAlgebraicZero
