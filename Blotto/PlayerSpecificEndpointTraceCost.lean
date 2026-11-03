import Blotto.PlayerSpecificEndpointExecution

/-! Complete operand-sized trace bounds for a cached Sturm endpoint query.
The current fixed-degree application has at most five rows of length four.
Preparing those rows and pricing the bisection traversal remain separate. -/
namespace Blotto.PlayerSpecificEndpointTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificEndpointExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

def width (H N M : ℕ) : ℕ := PlayerSpecificHornerTraceCost.width H N+M+16

theorem evalRows_fits (rows : List Data) (x : ℚ) (H N M : ℕ)
    (h : ∀ p∈rows,HasHeight p H ∧ p.length≤N) (hx : RationalHeight x H) (hlen : rows.length≤M) :
    Fits (width H N M) (evalRows rows x).2 := by
  have hHW : 1+2*H≤width H N M := by
    unfold width PlayerSpecificHornerTraceCost.width PlayerSpecificHornerTraceCost.valueHeight
    omega
  have hEW : 1+2*((2*H+1)*N+1)≤width H N M := by
    unfold width PlayerSpecificHornerTraceCost.width PlayerSpecificHornerTraceCost.valueHeight
    nlinarith
  have hMW : M+8≤width H N M := by unfold width; omega
  induction rows with
  | nil =>
    intro e he
    simp only [evalRows,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact (control_width 0).trans (by omega)
    · exact (rationalWordWidth_of_height hx).trans hHW
  | cons p rows ih =>
    have hp := h p List.mem_cons_self
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem p hq)) (by simp only [List.length_cons] at hlen; omega)
    have hhead := fits_mono (PlayerSpecificHornerTraceCost.evaluate_fits p x H N hp.1 hx hp.2)
      (show PlayerSpecificHornerTraceCost.width H N≤width H N M by unfold width; omega)
    have hvals := evalRows_height (p::rows) x H N h hx
    have hcopy := copyRow_fits (width H N M) (evalRows (p::rows) x).1
      (fun q hq => (rationalWordWidth_of_height (hvals q hq)).trans hEW)
      (by rw [evalRows_length]; exact (Nat.add_le_add_right hlen 1).trans (by omega))
    have hc : Fits (width H N M) [.control (rows.length+1)] := by
      intro e he
      have he' := List.mem_singleton.mp he
      subst e
      exact (control_width (rows.length+1)).trans (by simp only [List.length_cons] at hlen; omega)
    change Fits (width H N M) ((([.control (rows.length+1)]++(PlayerSpecificDenseExecution.evaluate p x).2)++
      (evalRows rows x).2)++copyRow ((evalRows (p::rows) x).1))
    simpa only [fits_append] using And.intro (And.intro (And.intro hc hhead) ht) hcopy

theorem run_fits (rows : List Data) (x : ℚ) (H N M : ℕ)
    (h : ∀ p∈rows,HasHeight p H ∧ p.length≤N) (hx : RationalHeight x H) (hlen : rows.length≤M) :
    Fits (width H N M) (run rows x).2 := by
  have he := evalRows_fits rows x H N M h hx hlen
  have hv := evalRows_height rows x H N h hx
  have hvl : (evalRows rows x).1.length≤M := by rw [evalRows_length]; exact hlen
  have hc := PlayerSpecificVariationTraceCost.run_fits_height (evalRows rows x).1 ((2*H+1)*N+1) M hv hvl
  have hc' := fits_mono hc (show PlayerSpecificVariationTraceCost.width ((2*H+1)*N+1) M≤width H N M by
    unfold width PlayerSpecificVariationTraceCost.width PlayerSpecificHornerTraceCost.width PlayerSpecificHornerTraceCost.valueHeight
    nlinarith)
  have hcount := PlayerSpecificVariationExecution.count_le_length (evalRows rows x).1
  rw [evalRows_length] at hcount
  have hMW : M+8≤width H N M := by unfold width; omega
  have hm : Fits (width H N M) [.control rows.length,.control (PlayerSpecificVariationExecution.run (evalRows rows x).1).1] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl <;> exact (control_width _).trans (by omega)
  simpa only [run,fits_append] using And.intro (And.intro he hc') hm

theorem run_trace_length (rows : List Data) (x : ℚ) (N M : ℕ)
    (h : ∀ p∈rows,p.length≤N) (hlen : rows.length≤M) :
    (run rows x).2.length≤(11*N+M+8)*(M+1)+20*(M+1)^2+2 := by
  have he := evalRows_trace_length rows x N M h hlen
  have hc := PlayerSpecificVariationExecution.trace_length (evalRows rows x).1
  rw [evalRows_length] at hc
  have hm := Nat.mul_le_mul_left (11*N+M+8) (Nat.add_le_add_right hlen 1)
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) 2
  simp only [run,List.length_append,List.length_cons,List.length_nil]
  nlinarith

theorem cubic_query_cost (model : RationalCostModel) (rows : List Data) (x : ℚ) (H : ℕ)
    (h : ∀ p∈rows,HasHeight p H ∧ p.length≤4) (hx : RationalHeight x H) (hlen : rows.length≤5) :
    price model (run rows x).2≤4000*model.rat (22*H+48) := by
  have hf := run_fits rows x H 4 5 h hx hlen
  have hp := price_bound model (width H 4 5) (by unfold width PlayerSpecificHornerTraceCost.width; omega) _ hf
  have hl := run_trace_length rows x 4 5 (fun p hp => (h p hp).2) hlen
  have hw : width H 4 5=22*H+48 := by
    unfold width PlayerSpecificHornerTraceCost.width PlayerSpecificHornerTraceCost.valueHeight
    ring
  rw [hw] at hp
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.reducePow] at hl
  nlinarith

end Blotto.PlayerSpecificEndpointTraceCost
