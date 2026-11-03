import Blotto.PlayerSpecificLeadingExecution

/-! Traced zero-padding monomials and their actual height/length/source price.
The numerical result is the original cancellation routine's monomial. -/
namespace Blotto.PlayerSpecificMonomialExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run : ℕ → ℚ → Data×Trace
  | 0,a => PlayerSpecificDenseExecution.finish [a] [.copy a,.control 0]
  | n+1,a =>
    let tail := run n a
    PlayerSpecificDenseExecution.finish (0::tail.1) (tail.2++[.copy 0,.control n])

theorem value (n : ℕ) (a : ℚ) : (run n a).1=PlayerSpecificPolynomialCancellation.monomial n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run,PlayerSpecificDenseExecution.finish,ih,PlayerSpecificPolynomialCancellation.monomial]

theorem length (n : ℕ) (a : ℚ) : (run n a).1.length=n+1 := by
  rw [value,PlayerSpecificCancellationHeights.monomial_length]

theorem height (n : ℕ) (a : ℚ) (H : ℕ) (ha : RationalHeight a H) (hH : 1≤H) : HasHeight (run n a).1 H := by
  rw [value]
  exact PlayerSpecificCancellationHeights.monomial_height n a H ha hH

theorem trace_length (n : ℕ) (a : ℚ) : (run n a).2.length≤(n+6)^2 := by
  induction n with
  | zero => simp only [run,PlayerSpecificDenseExecution.finish,List.length_append,copyRow_length,List.length_cons,List.length_nil]; norm_num
  | succ n ih =>
    simp only [run,PlayerSpecificDenseExecution.finish,List.length_append,copyRow_length,List.length_cons,List.length_nil,length]
    nlinarith

def width (H N : ℕ) : ℕ := 2*H+N+16

theorem fits (n : ℕ) (a : ℚ) (H N : ℕ) (ha : RationalHeight a H) (hH : 1≤H) (hn : n≤N) :
    Fits (width H N) (run n a).2 := by
  have hW : 1+2*H≤width H N := by unfold width; omega
  have hN : N+2≤width H N := by unfold width; omega
  induction n with
  | zero =>
    apply PlayerSpecificDenseTraceFits.finish_fits [a] _ (width H N) H (N+1) (cons_height ha (nil_height _))
      (by simp only [List.length_cons,List.length_nil]; omega) hW hN
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact (rationalWordWidth_of_height ha).trans hW
    · exact (control_width 0).trans (by omega)
  | succ n ih =>
    have ht := ih (by omega)
    have hv := height (n+1) a H ha hH
    have hl : (run (n+1) a).1.length≤N+1 := by rw [length]; omega
    have hp : Fits (width H N) [.copy 0,.control n] := by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl
      · exact (rationalWordWidth_of_height zero_height).trans (by unfold width; omega)
      · exact (control_width n).trans (by omega)
    apply PlayerSpecificDenseTraceFits.finish_fits _ _ (width H N) H (N+1) hv hl hW hN
    exact (fits_append _ _ _).mpr ⟨ht,hp⟩

theorem cost (model : RationalCostModel) (n : ℕ) (a : ℚ) (H N : ℕ)
    (ha : RationalHeight a H) (hH : 1≤H) (hn : n≤N) :
    price model (run n a).2≤3*(N+6)^2*model.rat (width H N) := by
  have hp := price_bound model (width H N) (by unfold width; omega) _ (fits n a H N ha hH hn)
  have hl := (trace_length n a).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hn 6) 2)
  have hm := Nat.mul_le_mul_right (3*model.rat (width H N)) hl
  nlinarith

end Blotto.PlayerSpecificMonomialExecution
