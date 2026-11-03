import Blotto.PlayerSpecificAlgebraicReduction

/-! Modular Horner multiplication keeps each actual dividend within four
coefficients for a cubic field, even when reducing a long inverse certificate. -/
namespace Blotto.PlayerSpecificModularHorner
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

def input (c : ℚ) (b rest : Data) : Data := add (scale c b) (shift rest)
def run (m b : Data) : Data → Data
  | [] => []
  | c::cs => reduce m (input c b (run m b cs))

theorem reduced (m b a : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (run m b a) := by
  cases a with
  | nil => exact nil_reduced m hm0
  | cons c cs => exact PlayerSpecificAlgebraicReduction.reduced m _ hm hm0

theorem real_value (m b a : Data) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (run m b a) x=realEvaluate a x*realEvaluate b x := by
  induction a with
  | nil => simp only [run,realEvaluate,List.foldr_nil,zero_mul]
  | cons c cs ih =>
    rw [run,real_reduce m _ x hx,input,real_add,real_scale,real_shift,ih]
    simp only [realEvaluate,List.foldr_cons]
    ring

theorem dividend_length (m b : Data) (hm : Normalized m) (hm0 : m≠[]) (hlen : m.length≤4)
    (hb : b.length≤3) (c : ℚ) (cs : Data) : (input c b (run m b cs)).length≤4 := by
  have hr:=(reduced m b cs hm hm0).2
  rw [input,add_length,scale_length]
  change max b.length ((run m b cs).length+1)≤4
  omega

def reduceLong (m a : Data) : Data := run m [1] a

theorem reduceLong_value (m a : Data) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (reduceLong m a) x=realEvaluate a x := by
  have h:=real_value m [1] a x hx
  simpa only [reduceLong,realEvaluate,List.foldr_cons,List.foldr_nil,Rat.cast_one,mul_zero,add_zero,mul_one] using h

end Blotto.PlayerSpecificModularHorner
