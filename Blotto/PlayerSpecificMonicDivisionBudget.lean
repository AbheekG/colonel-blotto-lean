import Blotto.PlayerSpecificMonicDivisionExecution

/-! Derived fixed-degree budgets for the actual monic recursion. Geometric
growth is only in the at-most-four-step fuel, so widths stay linear in H. -/
namespace Blotto.PlayerSpecificMonicDivisionBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def step (H : ℕ) : ℕ := 11*H+6
def postHeight (H : ℕ) : ℕ := 200000*(H+1)
def width (fuel H : ℕ) : ℕ := 1000000^(fuel+2)*(H+1)

theorem step_ge (H : ℕ) : H≤step H := by unfold step; omega
theorem post_ge (H : ℕ) : H≤postHeight H := by unfold postHeight; omega

theorem tail_height (H : ℕ) : 16105*step H+9665≤postHeight H := by unfold step postHeight; omega
theorem added_height (H : ℕ) : H+(16105*step H+9665)+1≤postHeight H := by unfold step postHeight; omega

theorem width_lower (fuel H : ℕ) : 1000000000000*(H+1)≤width fuel H := by
  have h := Nat.pow_le_pow_right (by decide : 0<(1000000:ℕ)) (show 2≤fuel+2 by omega)
  exact Nat.mul_le_mul_right (H+1) h

theorem width_large (fuel H : ℕ) : 6≤width fuel H := by have h:=width_lower fuel H; nlinarith

theorem dense_width (fuel H : ℕ) : 40*H+64≤width fuel H := by have h:=width_lower fuel H; nlinarith

theorem cancellation_width (fuel H : ℕ) : PlayerSpecificCancellationTraceCost.width H≤width fuel H := by
  have h:=width_lower fuel H
  unfold PlayerSpecificCancellationTraceCost.width
  nlinarith

theorem post_width (fuel H : ℕ) : 40*postHeight H+64≤width fuel H := by
  have h:=width_lower fuel H
  unfold postHeight
  nlinarith

theorem next_width (fuel H : ℕ) : width fuel (step H)≤width (fuel+1) H := by
  have h : step H+1≤1000000*(H+1) := by unfold step; omega
  have hm := Nat.mul_le_mul_left (1000000^(fuel+2)) h
  unfold width
  rw [show fuel+1+2=(fuel+2)+1 by omega,pow_succ (1000000:ℕ) (fuel+2),Nat.mul_assoc]
  exact hm

theorem width_cap (fuel H : ℕ) (hcap : fuel≤4) : width fuel H≤1000000^6*(H+1) :=
  Nat.mul_le_mul_right (H+1) (Nat.pow_le_pow_right (by decide) (by omega))

theorem copy_cost (model : RationalCostModel) (row : Data) (H W : ℕ) (hp : HasHeight row H)
    (hlen : row.length≤4) (hHW : 1+2*H≤W) (hW : 6≤W) : price model (copyRow row)≤15*model.rat W := by
  have hf := copyRow_fits W row (fun q hq => (rationalWordWidth_of_height (hp q hq)).trans hHW) (by omega)
  have hc := price_bound model W (by omega) _ hf
  rw [copyRow_length] at hc
  have hm := Nat.mul_le_mul_right (3*model.rat W) (show row.length+1≤5 by omega)
  nlinarith

theorem control_cost (model : RationalCostModel) (n W : ℕ) (hn : n≤4) (hW : 6≤W) :
    price model [.control n]≤3*model.rat W := by
  exact price_bound model W (by omega) _ (by
    intro e he
    have he' := List.mem_singleton.mp he
    subst e
    exact (control_width n).trans (by omega))

theorem header_cost (model : RationalCostModel) (q current : Data) (fuel H W : ℕ) (hq : HasHeight q H)
    (hql : q.length≤4) (hcl : current.length≤4) (hf : fuel≤4) (hHW : 1+2*H≤W) (hW : 6≤W) :
    price model (PlayerSpecificMonicDivisionExecution.header q fuel current)≤24*model.rat W := by
  have hcopy := copy_cost model q H W hq hql hHW hW
  have hc := PlayerSpecificDenseTraceFits.controls_fits W [fuel,current.length,q.length] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> omega)
  have hp := price_bound model W (by omega) _ hc
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hp
  rw [PlayerSpecificMonicDivisionExecution.header,price_append]
  nlinarith

end Blotto.PlayerSpecificMonicDivisionBudget
