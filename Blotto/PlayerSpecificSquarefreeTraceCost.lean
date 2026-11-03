import Blotto.PlayerSpecificPreparationBudget

/-! Complete squarefree preprocessing price from actual input heights. -/
namespace Blotto.PlayerSpecificSquarefreeTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificSquarefreeHeights PlayerSpecificPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem run_cost (model : RationalCostModel) (p : Data) (H : ℕ)
    (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    price model (PlayerSpecificSquarefreeExecution.run p).2≤3000000000*model.rat (width H) := by
  let differentiated := PlayerSpecificDenseExecution.derivative p
  let common := PlayerSpecificGCDExecution.run p differentiated.1
  let divided := PlayerSpecificDivisionExecution.run p common.1
  have hdH : HasHeight differentiated.1 (5*(H+1)) := by
    rw [PlayerSpecificDenseExecution.derivative_value]
    exact derivative_height_four p H hp hlen
  have hdl : differentiated.1.length≤4 := by
    rw [PlayerSpecificDenseExecution.derivative_value]
    exact (derivative_length p).trans hlen
  have hgvalue : common.1=PlayerSpecificSquarefreeAlgorithm.gcdDerivative p := by
    simp only [common,PlayerSpecificGCDExecution.value,differentiated,
      PlayerSpecificDenseExecution.derivative_value,PlayerSpecificSquarefreeAlgorithm.gcdDerivative]
  have hgH : HasHeight common.1 (gcdHeight H) := by rw [hgvalue]; exact (gcd_bounds p H hp hlen).1
  have hgl : common.1.length≤4 := by rw [hgvalue]; exact (gcd_bounds p H hp hlen).2
  have hresult : divided.1.1=(PlayerSpecificSquarefreeExecution.run p).1 := rfl
  have hb := PlayerSpecificSquarefreeExecution.bounds p H hp hH hlen
  have hd := PlayerSpecificDenseOperationCost.derivative_cost model p H 4 hp hlen
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hd
  have hdp := hd.trans (Nat.mul_le_mul_left 375000 (model.monotone (dense_width H H (input_height H))))
  have hg := PlayerSpecificGCDTraceCost.run_cost model p differentiated.1 (5*(H+1))
    (mono hp (by omega)) hdH (by omega) hlen hdl
  have hgp := hg.trans (Nat.mul_le_mul_left 2000000000 (model.monotone (cap_width H _ (derivative_height H))))
  have hv := PlayerSpecificDivisionTraceCost.run_cost model p common.1 (gcdHeight H)
    (mono hp (gcdHeight_ge H)) hgH (hH.trans (gcdHeight_ge H)) hlen hgl
  have hvp := hv.trans (Nat.mul_le_mul_left 100000000 (model.monotone (division_width H _ (gcd_height H))))
  have hW : 6≤width H := (by decide : 6≤32).trans (width_large H)
  have hcp := PlayerSpecificMonicDivisionBudget.copy_cost model p H (width H) hp hlen
    (copy_width H H (input_height H)) hW
  have hcr := PlayerSpecificMonicDivisionBudget.copy_cost model divided.1.1 (quotientHeight H) (width H)
    (by rw [hresult]; exact hb.1) (by rw [hresult]; exact hb.2)
    (copy_width H _ (quotient_height H)) hW
  have hc := PlayerSpecificMonicDivisionBudget.control_cost model p.length (width H) hlen hW
  change price model (copyRow p++differentiated.2++common.2++divided.2++copyRow divided.1.1++[.control p.length])≤_
  simp only [price_append]
  nlinarith

end Blotto.PlayerSpecificSquarefreeTraceCost
