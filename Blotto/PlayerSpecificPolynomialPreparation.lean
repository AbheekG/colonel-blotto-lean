import Blotto.PlayerSpecificSturmRunCost

/-! Cached polynomial part of root preparation, from original coefficient
data. Squarefree polynomial, separation certificate and Sturm rows are each
computed once. Integer enclosure/depth preparation is a separate step. -/
namespace Blotto.PlayerSpecificPolynomialPreparation
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificSquarefreeHeights PlayerSpecificPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 6000000

structure Result where
  polynomial : Data
  unitRight : Data
  rows : List Data

def run (p : Data) : Result×Trace :=
  let certified := PlayerSpecificCertificateExecution.run p
  let sequence := PlayerSpecificSturmExecution.run certified.1.1
  let result : Result := ⟨certified.1.1,certified.1.2,sequence.1⟩
  (result,certified.2++sequence.2++copyRow result.polynomial++copyRow result.unitRight++
    PlayerSpecificSturmExecution.copyRows result.rows++[.control result.polynomial.length,.control result.unitRight.length,.control result.rows.length])

theorem values (p : Data) :
    (run p).1.polynomial=PlayerSpecificSquarefreeAlgorithm.run p ∧
      (run p).1.unitRight=PlayerSpecificSquarefreeCoprime.unitRight p ∧
      (run p).1.rows=PlayerSpecificSturmRootCount.rows p := by
  simp only [run,PlayerSpecificCertificateExecution.polynomial_value,PlayerSpecificCertificateExecution.unit_value,
    PlayerSpecificSturmExecution.value,PlayerSpecificSturmRootCount.rows,and_self]

theorem run_cost (model : RationalCostModel) (p : Data) (H : ℕ)
    (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    price model (run p).2≤10000000000*model.rat (width H) := by
  let certified := PlayerSpecificCertificateExecution.run p
  let sequence := PlayerSpecificSturmExecution.run certified.1.1
  have hb:=PlayerSpecificCertificateExecution.bounds p H hp hH hlen
  have hqH : HasHeight certified.1.1 (quotientHeight H) := hb.1
  have huH : HasHeight certified.1.2 (2*certificateHeight H) := hb.2.1
  have hql : certified.1.1.length≤4 := hb.2.2.1
  have hul : certified.1.2.length≤17 := hb.2.2.2
  have hrows : sequence.1=PlayerSpecificSturmRootCount.rows p := by
    simp only [sequence,PlayerSpecificSturmExecution.value,certified,PlayerSpecificCertificateExecution.polynomial_value,
      PlayerSpecificSturmRootCount.rows]
  have hrH : ∀ row∈sequence.1,HasHeight row (certificateHeight H) ∧ row.length≤4 := by
    rw [hrows]; exact PlayerSpecificSturmHeights.rows_bounds p H hp hH hlen
  have hrl : sequence.1.length≤5 := by rw [hrows]; exact PlayerSpecificSturmHeights.rows_length p H hp hH hlen
  have hc:=PlayerSpecificCertificateTraceCost.run_cost model p H hp hH hlen
  have hs:=PlayerSpecificSturmRunCost.run_cost model certified.1.1 (quotientHeight H) hqH
    (hH.trans (quotientHeight_ge H)) hql
  have hsp:=hs.trans (Nat.mul_le_mul_left 2000000000 (model.monotone (cap_width H _ (certificate_input H))))
  have hW:=width_large H
  have hqc:=PlayerSpecificExtendedCopyCost.row_cost model certified.1.1 (quotientHeight H) (width H)
    hqH (by omega) (copy_width H _ (quotient_height H)) hW
  have huc:=PlayerSpecificExtendedCopyCost.row_cost model certified.1.2 (2*certificateHeight H) (width H)
    huH (by omega) (copy_width H _ (unit_height H)) hW
  have hrc:=PlayerSpecificSturmCopyCost.copyRows_cost model sequence.1 (certificateHeight H) (width H)
    hrH hrl (copy_width H _ (certificate_height H)) hW
  have hf:=PlayerSpecificDenseTraceFits.controls_fits (width H) [certified.1.1.length,certified.1.2.length,sequence.1.length] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> omega)
  have hm:=price_bound model (width H) (by omega) _ hf
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hm
  change price model (certified.2++sequence.2++copyRow certified.1.1++copyRow certified.1.2++
    PlayerSpecificSturmExecution.copyRows sequence.1++[.control certified.1.1.length,.control certified.1.2.length,.control sequence.1.length])≤_
  simp only [price_append]
  nlinarith

theorem actual_contract (model : RationalCostModel) (p : Data) (hlen : p.length≤4) :
    let H := PlayerSpecificRationalMagnitude.inputHeight p
    (run p).1.polynomial=PlayerSpecificSquarefreeAlgorithm.run p ∧
      (run p).1.unitRight=PlayerSpecificSquarefreeCoprime.unitRight p ∧
      (run p).1.rows=PlayerSpecificSturmRootCount.rows p ∧
      HasHeight (run p).1.polynomial (quotientConstant*(H+1)) ∧
      HasHeight (run p).1.unitRight (2*certificateConstant*(H+1)) ∧
      (run p).1.polynomial.length≤4 ∧ (run p).1.unitRight.length≤17 ∧ (run p).1.rows.length≤5 ∧
      (∀ row∈(run p).1.rows,HasHeight row (certificateConstant*(H+1)) ∧ row.length≤4) ∧
      price model (run p).2≤10000000000*model.rat (linearCoefficient*(H+1)) := by
  dsimp only
  let H:=PlayerSpecificRationalMagnitude.inputHeight p
  have hp : HasHeight p H := PlayerSpecificRationalMagnitude.member_height p
  have hH : 1≤H := by unfold H PlayerSpecificRationalMagnitude.inputHeight; omega
  have hv:=values p
  have hq:=quotient_bounds p H hp hH hlen
  have hu:=unitRight_bounds p H hp hH hlen
  have hr:=PlayerSpecificSturmHeights.rows_bounds p H hp hH hlen
  have hl:=PlayerSpecificSturmHeights.rows_length p H hp hH hlen
  have hc:=run_cost model p H hp hH hlen
  refine ⟨hv.1,hv.2.1,hv.2.2,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hv.1]; exact mono hq.1 (quotient_linear H)
  · rw [hv.2.1]; exact mono hu.1 (by have hm:=Nat.mul_le_mul_left 2 (certificate_linear H); nlinarith)
  · rw [hv.1]; exact hq.2
  · rw [hv.2.1]; exact hu.2
  · rw [hv.2.2]; exact hl
  · rw [hv.2.2]
    intro row hrow
    exact ⟨mono (hr row hrow).1 (certificate_linear H),(hr row hrow).2⟩
  · exact hc.trans (Nat.mul_le_mul_left 10000000000 (model.monotone (width_linear H)))

end Blotto.PlayerSpecificPolynomialPreparation
