import Blotto.PlayerSpecificDivisionExecution

/-! Complete fixed-degree source price for arbitrary rational polynomial
division, including a zero divisor, normalization and quotient rescaling. -/
namespace Blotto.PlayerSpecificDivisionTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 7000000

def width (H : ℕ) : ℕ := 2*1000000^6*(H+1)

theorem width_lower (H : ℕ) : 1000000000000*(H+1)≤width H := by
  have h : (1000000000000:ℕ)≤2*1000000^6 := by norm_num
  exact Nat.mul_le_mul_right (H+1) h

theorem width_large (H : ℕ) : 6≤width H := by have h:=width_lower H; nlinarith

theorem dense_width (H : ℕ) : 40*H+64≤width H := by have h:=width_lower H; nlinarith

theorem output_width (H : ℕ) : 40*(32211*H+9666)+64≤width H := by have h:=width_lower H; nlinarith

theorem monic_width (H : ℕ) : 1000000^6*(2*H+1)≤width H := by
  calc
    _ ≤ 1000000^6*(2*(H+1)) := Nat.mul_le_mul_left _ (by omega)
    _ = width H := by unfold width; ring

theorem scale_height_bound (H : ℕ) : H+(32210*H+9665)≤32211*H+9666 := by omega
theorem inverse_height_bound (H : ℕ) : H≤32211*H+9666 := by omega
theorem quotient_height_bound (H : ℕ) : 32210*H+9665≤32211*H+9666 := by omega
theorem copy_width (H : ℕ) : 1+2*(32211*H+9666)≤width H := by
  have h:=output_width H
  nlinarith

theorem run_cost (model : RationalCostModel) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    price model (PlayerSpecificDivisionExecution.run p q).2≤100000000*model.rat (width H) := by
  let divisor := PlayerSpecificDenseExecution.trim q
  have hdH : HasHeight divisor.1 H := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hq
  have hdl : divisor.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length q).trans hql
  have hdn : Normalized divisor.1 := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_normalized _
  have hW := width_large H
  have hDW := dense_width H
  have hOutW := output_width H
  have hdt := PlayerSpecificDenseOperationCost.trim_cost model q H 4 hq hql
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hdt
  have hdtp : price model divisor.2≤375000*model.rat (width H) :=
    hdt.trans (Nat.mul_le_mul_left 375000 (model.monotone hDW))
  have hpcopy := PlayerSpecificMonicDivisionBudget.copy_cost model p H (width H) hp hpl (by omega) hW
  have he := PlayerSpecificMonicDivisionBudget.copy_cost model [] H (width H) (nil_height _)
    (by simp only [List.length_nil]; omega) (by omega) hW
  have hf0 := PlayerSpecificMonicDivisionBudget.control_cost model 0 (width H) (by omega) hW
  have hf1 := PlayerSpecificMonicDivisionBudget.control_cost model 1 (width H) (by omega) hW
  have hmeta : Fits (width H) [.control p.length,.control divisor.1.length] := by
    intro e hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> exact (control_width _).trans (by omega)
  have hmp := price_bound model (width H) (by omega) _ hmeta
  simp only [List.length_cons,List.length_nil] at hmp
  rw [PlayerSpecificDivisionExecution.run]
  split
  · let remainder := PlayerSpecificDenseExecution.trim p
    have ht := PlayerSpecificDenseOperationCost.trim_cost model p H 4 hp hpl
    rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ht
    have htp : price model remainder.2≤375000*model.rat (width H) :=
      ht.trans (Nat.mul_le_mul_left 375000 (model.monotone hDW))
    change price model (divisor.2++copyRow p++[.control p.length,.control divisor.1.length]++remainder.2++copyRow []++[.control 0])≤_
    simp only [price_append]
    nlinarith
  · rename_i hn
    let normalized := PlayerSpecificMonicizeExecution.run divisor.1
    let divided := PlayerSpecificMonicDivisionExecution.run normalized.1.2 p.length p
    let scaled := PlayerSpecificDenseExecution.scale normalized.1.1 divided.1.1
    let quotient := PlayerSpecificDenseExecution.trim scaled.1
    have hiH : RationalHeight normalized.1.1 H := PlayerSpecificMonicizeExecution.inverse_height divisor.1 H hdH hH
    have hqH : HasHeight normalized.1.2 (2*H) := PlayerSpecificMonicizeExecution.polynomial_height divisor.1 H hdH hH
    have hql' : normalized.1.2.length≤4 := (PlayerSpecificMonicizeExecution.polynomial_length divisor.1).trans hdl
    have hqn' : Normalized normalized.1.2 := PlayerSpecificMonicizeExecution.normalized divisor.1
    have hqm' : (semantics normalized.1.2).Monic := PlayerSpecificMonicizeExecution.monic divisor.1 hdn hn
    have htwo : 1≤2*H := by omega
    have hph := mono hp (show H≤2*H by omega)
    have hdiv := PlayerSpecificMonicDivisionTraceCost.fixed_cost model normalized.1.2 p (2*H) hqn' hqm' hql' hph hqH htwo hpl
    have hdivp : price model divided.2≤50000000*model.rat (width H) :=
      hdiv.trans (Nat.mul_le_mul_left 50000000 (model.monotone (monic_width H)))
    have hh := PlayerSpecificMonicDivisionExecution.bounded_heights normalized.1.2 p.length p (2*H) hqH hph hql' htwo hpl
    have hheight : 16105*(2*H)+9665=32210*H+9665 := by ring
    rw [hheight] at hh
    have hqq : HasHeight divided.1.1 (32210*H+9665) := hh.1
    have hrr : HasHeight divided.1.2 (32210*H+9665) := hh.2
    have hls := PlayerSpecificMonicDivisionExecution.lengths normalized.1.2 p.length p hqn' hqm'
    have hqql : divided.1.1.length≤4 := hls.1.trans hpl
    have hrrl : divided.1.2.length≤4 := hls.2.trans hpl
    have hsH : HasHeight scaled.1 (32211*H+9666) := by
      rw [PlayerSpecificDenseExecution.scale_value]
      exact mono (s := H+(32210*H+9665)) (t := 32211*H+9666) (scale_height hiH hqq) (scale_height_bound H)
    have hsl : scaled.1.length≤4 := by
      rw [PlayerSpecificDenseExecution.scale_value,PlayerSpecificDensePolynomial.scale_length]
      exact hqql
    have hscale := PlayerSpecificDenseOperationCost.scale_cost model normalized.1.1 divided.1.1 (32211*H+9666) 4
      (hiH.mono (s := H) (t := 32211*H+9666) (inverse_height_bound H))
      (mono (s := 32210*H+9665) (t := 32211*H+9666) hqq (quotient_height_bound H)) hqql
    rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hscale
    have hscalep : price model scaled.2≤375000*model.rat (width H) :=
      hscale.trans (Nat.mul_le_mul_left 375000 (model.monotone hOutW))
    have hquot := PlayerSpecificDenseOperationCost.trim_cost model scaled.1 (32211*H+9666) 4 hsH hsl
    rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hquot
    have hquotp : price model quotient.2≤375000*model.rat (width H) :=
      hquot.trans (Nat.mul_le_mul_left 375000 (model.monotone hOutW))
    have hremcopy := PlayerSpecificMonicDivisionBudget.copy_cost model divided.1.2 (32211*H+9666) (width H)
      (mono (s := 32210*H+9665) (t := 32211*H+9666) hrr (quotient_height_bound H)) hrrl (copy_width H) hW
    have hnorm := PlayerSpecificMonicizeExecution.cost model divisor.1 H hdH hH hdl
    have hnormp : price model normalized.2≤1000000*model.rat (width H) :=
      hnorm.trans (Nat.mul_le_mul_left 1000000 (model.monotone (by
        have hl:=width_lower H
        unfold PlayerSpecificMonicizeExecution.width
        nlinarith)))
    change price model (divisor.2++copyRow p++[.control p.length,.control divisor.1.length]++normalized.2++divided.2++
      scaled.2++quotient.2++copyRow divided.1.2++[.control 1])≤_
    simp only [price_append]
    nlinarith

end Blotto.PlayerSpecificDivisionTraceCost
