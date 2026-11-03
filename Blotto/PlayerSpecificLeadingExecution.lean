import Blotto.PlayerSpecificDenseOperationCost

/-! Executed leading-coefficient reads and total inverse-leading arithmetic,
with numerical refinements and actual operand/control source prices. -/
namespace Blotto.PlayerSpecificLeadingExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def readLast : Data → ℚ×Trace
  | [] => (0,[.copy 0,.control 0])
  | [a] => (a,[.copy a,.control 1])
  | a::b::p =>
    let rest := readLast (b::p)
    (rest.1,[.copy a,.control (p.length+2)]++rest.2++[.copy rest.1])

theorem readLast_value (p : Data) : (readLast p).1=p.getLast?.getD 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil => rfl
    | cons b p => simpa only [readLast,List.getLast?_cons_cons] using ih

theorem readLast_height (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) : RationalHeight (readLast p).1 H := by
  rw [readLast_value]
  exact default_height hp hH

theorem readLast_trace_length (p : Data) : (readLast p).2.length≤4*p.length+2 := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih =>
    cases p with
    | nil => simp only [readLast,List.length_cons,List.length_nil]; omega
    | cons b p =>
      simp only [readLast,List.length_append,List.length_cons,List.length_nil] at ih ⊢
      omega

def width (H N : ℕ) : ℕ := 2*H+N+8

theorem readLast_fits (p : Data) (H N : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤N) :
    Fits (width H N) (readLast p).2 := by
  have hW : 1+2*H≤width H N := by unfold width; omega
  induction p with
  | nil =>
    intro e he
    simp only [readLast,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact (rationalWordWidth_of_height zero_height).trans (by unfold width; omega)
    · exact (control_width 0).trans (by unfold width; omega)
  | cons a p ih =>
    cases p with
    | nil =>
      intro e he
      simp only [readLast,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl
      · exact (rationalWordWidth_of_height (head_height hp)).trans hW
      · exact (control_width 1).trans (by unfold width; omega)
    | cons b p =>
      have htail := tail_height hp
      have htl : (b::p).length≤N := by simp only [List.length_cons] at hlen ⊢; omega
      have ht := ih htail htl
      have hv := readLast_height (b::p) H htail hH
      have hfront : Fits (width H N) [.copy a,.control (p.length+2)] := by
        intro e he
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl
        · exact (rationalWordWidth_of_height (head_height hp)).trans hW
        · exact (control_width _).trans (by simp only [List.length_cons] at hlen; unfold width; omega)
      have hback : Fits (width H N) [.copy (readLast (b::p)).1] := by
        intro e he
        have he' := List.mem_singleton.mp he
        subst e
        exact (rationalWordWidth_of_height hv).trans hW
      simpa only [readLast,fits_append] using And.intro (And.intro hfront ht) hback

theorem readLast_cost (model : RationalCostModel) (p : Data) (H N : ℕ)
    (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤N) :
    price model (readLast p).2≤(12*N+6)*model.rat (width H N) := by
  have h := price_bound model (width H N) (by unfold width; omega) _ (readLast_fits p H N hp hH hlen)
  have hl := (readLast_trace_length p).trans (show 4*p.length+2≤4*N+2 by omega)
  have hm := Nat.mul_le_mul_right (3*model.rat (width H N)) hl
  nlinarith

def inverseLead (p : Data) : ℚ×Trace :=
  let leading := readLast p
  let inverted := scalar .divide 1 leading.1
  (inverted.1,leading.2++inverted.2)

theorem inverseLead_value (p : Data) : (inverseLead p).1=PlayerSpecificPolynomialDivision.inverseLead p := by
  simp only [inverseLead,scalar,Arithmetic.apply,readLast_value,one_div,PlayerSpecificPolynomialDivision.inverseLead]

theorem inverseLead_height (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) :
    RationalHeight (inverseLead p).1 H := by
  rw [inverseLead_value]
  exact (default_height hp hH).inv

theorem inverseLead_cost (model : RationalCostModel) (p : Data) (H N : ℕ)
    (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤N) :
    price model (inverseLead p).2≤(12*N+21)*model.rat (width H N) := by
  have hr := readLast_cost model p H N hp hH hlen
  have hv := readLast_height p H hp hH
  have hW : 1+2*H≤width H N := by unfold width; omega
  have hinv : RationalHeight (Arithmetic.divide.apply 1 (readLast p).1) H := by simpa only [Arithmetic.apply,one_div] using hv.inv
  have hs := scalar_fits (width H N) .divide 1 (readLast p).1
    ((rationalWordWidth_of_height (one_height.mono hH)).trans hW)
    ((rationalWordWidth_of_height hv).trans hW) ((rationalWordWidth_of_height hinv).trans hW) (by unfold width; omega)
  have hc := price_bound model (width H N) (by unfold width; omega) _ hs
  rw [scalar_length] at hc
  rw [inverseLead,price_append]
  nlinarith

end Blotto.PlayerSpecificLeadingExecution
