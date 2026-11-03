import Blotto.PlayerSpecificFactorHeights

/-! The actual signed linear-factor constructor includes the negation and
complete returned-row copies in its source trace. -/
namespace Blotto.PlayerSpecificLinearFactorExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1000000

def run (q : ℚ) : Data×Trace :=
  let negated:=scalar .multiply (-1) q
  let result:=[negated.1,1]
  (result,negated.2++copyRow result)

theorem value (q : ℚ) : (run q).1=PlayerSpecificLinearFactor.linear q := by
  simp only [run,scalar,Arithmetic.apply,neg_one_mul,PlayerSpecificLinearFactor.linear]

theorem run_cost (model : RationalCostModel) (q : ℚ) (H : ℕ)
    (hq : RationalHeight q H) (hH : 1≤H) : price model (run q).2≤60*model.rat (8*H+16) := by
  have hneg : RationalHeight (-1:ℚ) H := one_height.neg.mono hH
  have hs:=scalar_fits_height .multiply (-1) q H hneg hq
  have hr : HasHeight (run q).1 H := by
    rw [value]
    exact PlayerSpecificFactorHeights.linear_height q H hq hH
  have hrow:=copyRow_fits (8*H+16) (run q).1
    (fun x hx => (rationalWordWidth_of_height (hr x hx)).trans (by omega))
    (by rw [value]; simp only [PlayerSpecificLinearFactor.linear,List.length_cons,List.length_nil]; omega)
  have hfit: Fits (8*H+16) (run q).2 :=
    (fits_append _ _ _).mpr ⟨fits_mono hs (by omega),hrow⟩
  have hc:=price_bound model (8*H+16) (by omega) _ hfit
  have hl : (run q).2.length=8 := by
    simp only [run,List.length_append,scalar_length,copyRow_length,List.length_cons,List.length_nil]
  rw [hl] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (by decide : 3*8≤60))

end Blotto.PlayerSpecificLinearFactorExecution
