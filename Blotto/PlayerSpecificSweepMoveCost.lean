import Blotto.PlayerSpecificSweepInitialCost

/-! Constant-work rational sweep move at the actual additive coefficient
height. The two fresh quotient terms, all accumulator updates, maximum
comparison, complete input/output copies and branch word are priced. -/
namespace Blotto.PlayerSpecificSweepMoveCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalSweepHeights
open PlayerSpecificSweep PlayerSpecificRationalTrace PlayerSpecificSweepExecution PlayerSpecificSweepTraceFits
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem fits (s : State ℚ) (v w : ℚ) (T H : ℕ) (hs : StateHeight s T)
    (hv : RationalHeight v H) (hw : RationalHeight w H) :
    Fits (width (stepBound T H) 0) (PlayerSpecificSweepExecution.move s v w).2 := by
  let M:=stepBound T H
  let W:=width M 0
  have hT : T≤M := by unfold M stepBound; omega
  have hH : H≤M := by unfold M stepBound; omega
  have h3H : 3*H≤M := by unfold M stepBound; omega
  have hWM : 1+2*M≤W := by unfold W width; omega
  have hW : 6≤W := by unfold W width; omega
  have hsM:=state_mono s T M hs hT
  have hvM:=hv.mono hH
  have hwM:=hw.mono hH
  have hsquareV : RationalHeight (scalar .multiply v v).1 M := by
    simpa only [scalar_value,Arithmetic.apply] using (hv.mul hv).mono (show H+H≤M by omega)
  have hsquareW : RationalHeight (scalar .multiply w w).1 M := by
    simpa only [scalar_value,Arithmetic.apply] using (hw.mul hw).mono (show H+H≤M by omega)
  have htermV : RationalHeight (scalar .divide (scalar .multiply v v).1 w).1 M := by
    simpa only [scalar_value,Arithmetic.apply,pow_two] using (square_divide v w H hv hw).mono h3H
  have htermW : RationalHeight (scalar .divide (scalar .multiply w w).1 v).1 M := by
    simpa only [scalar_value,Arithmetic.apply,pow_two] using (square_divide w v H hw hv).mono h3H
  have scalar_fit (op : Arithmetic) (a b : ℚ) (ha : RationalHeight a M) (hb : RationalHeight b M) :
      Fits W (scalar op a b).2 :=
    fits_mono (scalar_fits_height op a b M ha hb) (by unfold W width; omega)
  have hsqV:=scalar_fit .multiply v v hvM hvM
  have htermVfit:=scalar_fit .divide _ w hsquareV hwM
  have hsqW:=scalar_fit .multiply w w hwM hwM
  have htermWfit:=scalar_fit .divide _ v hsquareW hvM
  have hfirst:=scalar_fit .subtract s.coefficients.A1 w hsM.1 hwM
  have hsecond:=scalar_fit .add s.coefficients.A2 _ hsM.2.1 htermV
  have hthird:=scalar_fit .subtract s.coefficients.B1 _ hsM.2.2.1 htermW
  have hfourth:=scalar_fit .add s.coefficients.B2 v hsM.2.2.2.1 hvM
  have hcompare:=compare_fits W s.prefixMax v
    ((rationalWordWidth_of_height hsM.2.2.2.2).trans hWM)
    ((rationalWordWidth_of_height hvM).trans hWM) (by omega)
  have hinput:=copy_state_fits s M W hsM hWM hW
  have hpair:=copyRow_fits W [v,w] (fun q hq =>
    (rationalWordWidth_of_height ((cons_height hvM (cons_height hwM (nil_height _))) q hq)).trans hWM) (by simp; omega)
  have hreturn : StateHeight (PlayerSpecificSweepExecution.move s v w).1 M := by
    rw [move_value]
    exact move_height s v w T H hs hv hw
  have hout:=copy_state_fits _ M W hreturn hWM hW
  have hcontrol : Fits W [.control (if (PlayerSpecificRationalTrace.compare s.prefixMax v).1 then 1 else 0)] := by
    intro e he
    have heq:=List.mem_singleton.mp he
    subst e
    exact (PlayerSpecificRationalTrace.control_width _).trans (by split <;> omega)
  simp only [PlayerSpecificSweepExecution.move] at hout ⊢
  simp only [fits_append]
  tauto

theorem source_cost (model : RationalCostModel) (s : State ℚ) (v w : ℚ) (T H : ℕ)
    (hs : StateHeight s T) (hv : RationalHeight v H) (hw : RationalHeight w H) :
    price model (PlayerSpecificSweepExecution.move s v w).2≤180*model.rat (width (stepBound T H) 0) := by
  have hp:=price_bound model (width (stepBound T H) 0) (by unfold width; omega) _ (fits s v w T H hs hv hw)
  rwa [move_length] at hp

end Blotto.PlayerSpecificSweepMoveCost
