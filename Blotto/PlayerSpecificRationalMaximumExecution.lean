import Blotto.PlayerSpecificSweepMoveCost

/-! Actual priced rational maximum, including operand/output copies and
the selected branch tag. Its return retains the input coefficient height. -/
namespace Blotto.PlayerSpecificRationalMaximumExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1500000

def run (a b : ℚ) : ℚ×Trace :=
  let compared:=PlayerSpecificRationalTrace.compare a b
  let result:=if compared.1 then b else a
  (result,compared.2++copyRow [a,b,result]++[.control (if compared.1 then 1 else 0)])
theorem value (a b : ℚ) : (run a b).1=max a b := by
  by_cases h : a≤b
  · simp only [run,PlayerSpecificRationalTrace.compare,h,decide_true,ite_true,max_eq_right h]
  · simp only [run,PlayerSpecificRationalTrace.compare,h,decide_false,Bool.false_eq_true,ite_false,
      max_eq_left ((lt_of_not_ge h).le)]
theorem length (a b : ℚ) : (run a b).2.length=9 := by
  simp only [run,List.length_append,compare_length,copyRow_length,List.length_cons,List.length_nil]
theorem fits (a b : ℚ) (H W : ℕ) (ha : RationalHeight a H) (hb : RationalHeight b H)
    (hH : 1+2*H≤W) (hW : 6≤W) : Fits W (run a b).2 := by
  have hc:=compare_fits W a b ((rationalWordWidth_of_height ha).trans hH)
    ((rationalWordWidth_of_height hb).trans hH) (by omega)
  have hout : RationalHeight (run a b).1 H := by rw [value]; exact PlayerSpecificRationalSweepHeights.max_height a b H ha hb
  have hrow:=copyRow_fits W [a,b,(run a b).1]
    (fun q hq => (rationalWordWidth_of_height ((cons_height ha (cons_height hb (cons_height hout (nil_height _)))) q hq)).trans hH)
    (by simp; omega)
  have ht : Fits W [.control (if (PlayerSpecificRationalTrace.compare a b).1 then 1 else 0)] := by
    intro e he
    have heq:=List.mem_singleton.mp he
    subst e
    exact (PlayerSpecificRationalTrace.control_width _).trans (by split <;> omega)
  simp only [run] at hrow ⊢
  exact (fits_append _ _ _).mpr ⟨(fits_append _ _ _).mpr ⟨hc,hrow⟩,ht⟩
theorem source_cost (model : RationalCostModel) (a b : ℚ) (H W : ℕ) (ha : RationalHeight a H)
    (hb : RationalHeight b H) (hH : 1+2*H≤W) (hW : 6≤W) : price model (run a b).2≤27*model.rat W := by
  have hp:=price_bound model W (by omega) _ (fits a b H W ha hb hH hW)
  rwa [length] at hp

end Blotto.PlayerSpecificRationalMaximumExecution
