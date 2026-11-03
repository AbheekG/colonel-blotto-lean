import Blotto.PlayerSpecificDenseExecution

/-! A priced refinement of actual rational endpoint Horner evaluation.
All operand/result/control widths follow from the input coefficient and
endpoint heights. No intermediate-value or cost oracle is supplied. -/
namespace Blotto.PlayerSpecificHornerTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def valueHeight (H N : ℕ) : ℕ := (2*H+1)*(N+1)+H+2
def width (H N : ℕ) : ℕ := 1+2*valueHeight H N+N+8

theorem width_pos (H N : ℕ) : 1≤width H N := by unfold width; omega

theorem evaluate_fits (p : Data) (x : ℚ) (H N : ℕ) (hp : HasHeight p H) (hx : RationalHeight x H)
    (hlen : p.length≤N) : Fits (width H N) (PlayerSpecificDenseExecution.evaluate p x).2 := by
  have hHW : 1+2*H≤width H N := by unfold width valueHeight; omega
  have hEW : 1+2*valueHeight H N≤width H N := by unfold width; omega
  have hNW : N+1≤width H N := by unfold width; omega
  induction p with
  | nil =>
    intro e he
    simp only [PlayerSpecificDenseExecution.evaluate,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · exact (rationalWordWidth_of_height hx).trans hHW
    · exact (rationalWordWidth_of_height zero_height).trans (by unfold width valueHeight; omega)
    · exact width_pos H N
  | cons a p ih =>
    have ht := ih (tail_height hp) (by simp only [List.length_cons] at hlen; omega)
    have ha := head_height hp
    have hv := evaluate_height (tail_height hp) hx
    rw [← PlayerSpecificDenseExecution.evaluate_value] at hv
    have hprod := hx.mul hv
    have hsum := ha.add hprod
    have hsize : p.length+1≤N := hlen
    have hm := Nat.mul_le_mul_left (2*H+1) hsize
    have hprodbound : H+((H+H+1)*p.length+1)≤valueHeight H N := by unfold valueHeight; nlinarith
    have hsumbound : H+(H+((H+H+1)*p.length+1))+1≤valueHeight H N := by unfold valueHeight; nlinarith
    have hpW := (rationalWordWidth_of_height (hprod.mono hprodbound)).trans hEW
    have hsW := (rationalWordWidth_of_height (hsum.mono hsumbound)).trans hEW
    have htW := (rationalWordWidth_of_height (hv.mono (by unfold valueHeight; nlinarith))).trans hEW
    have hxW := (rationalWordWidth_of_height hx).trans hHW
    have haW := (rationalWordWidth_of_height ha).trans hHW
    have hmtrace := scalar_fits (width H N) .multiply x (PlayerSpecificDenseExecution.evaluate p x).1 hxW htW hpW (width_pos H N)
    have hatrace := scalar_fits (width H N) .add a (scalar .multiply x (PlayerSpecificDenseExecution.evaluate p x).1).1
      haW hpW hsW (width_pos H N)
    have hc : Fits (width H N) [.control (p.length+1)] := by
      intro e he
      have he' := List.mem_singleton.mp he
      subst e
      exact (control_width (p.length+1)).trans (by unfold width; omega)
    change Fits (width H N) ([.control (p.length+1)]++(PlayerSpecificDenseExecution.evaluate p x).2++
      (scalar .multiply x (PlayerSpecificDenseExecution.evaluate p x).1).2++
      (scalar .add a (scalar .multiply x (PlayerSpecificDenseExecution.evaluate p x).1).1).2)
    simpa only [fits_append] using And.intro (And.intro (And.intro hc ht) hmtrace) hatrace

theorem evaluate_cost (model : RationalCostModel) (p : Data) (x : ℚ) (H N : ℕ)
    (hp : HasHeight p H) (hx : RationalHeight x H) (hlen : p.length≤N) :
    price model (PlayerSpecificDenseExecution.evaluate p x).2≤
      (33*p.length+9)*model.rat (width H N) := by
  have h := price_bound model (width H N) (width_pos H N) _ (evaluate_fits p x H N hp hx hlen)
  rw [PlayerSpecificDenseExecution.evaluate_trace_length] at h
  nlinarith

end Blotto.PlayerSpecificHornerTraceCost
