import Blotto.PlayerSpecificDenseTraceLength

/-! Actual trace lengths for subtraction, dense multiplication and
differentiation. Returned-list copies are included in these bounds. -/
namespace Blotto.PlayerSpecificCompositeTraceLength
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem subtract_length (p q : Data) (N : ℕ) (hp : p.length≤N) (hq : q.length≤N) :
    (PlayerSpecificDenseExecution.subtract p q).2.length≤
      (N+8)*(N+1)+(N+10)*(2*N+1)+N+1 := by
  have hs := PlayerSpecificDenseTraceLength.scale_length (-1) q N hq
  have hn : (PlayerSpecificDenseExecution.scale (-1) q).1.length=q.length := by
    rw [PlayerSpecificDenseExecution.scale_value,PlayerSpecificDensePolynomial.scale_length]
  have ha := PlayerSpecificDenseTraceLength.add_length p (PlayerSpecificDenseExecution.scale (-1) q).1 N hp (hn.le.trans hq)
  have hv : (PlayerSpecificDenseExecution.add p (PlayerSpecificDenseExecution.scale (-1) q).1).1.length≤N := by
    rw [PlayerSpecificDenseExecution.add_value,PlayerSpecificDensePolynomial.add_length,hn]
    exact max_le hp hq
  have hsm := Nat.mul_le_mul_left (N+8) (Nat.add_le_add_right hq 1)
  have ham := Nat.mul_le_mul_left (N+10) (show p.length+(PlayerSpecificDenseExecution.scale (-1) q).1.length+1≤2*N+1 by omega)
  simp only [PlayerSpecificDenseExecution.subtract,PlayerSpecificDenseExecution.finish,List.length_append,copyRow_length]
  nlinarith

def recursiveLength (N : ℕ) : ℕ := 100*(N+1)^2

theorem multiply_length (p q : Data) (N : ℕ) (hp : p.length≤N) (hq : q.length≤N) :
    (PlayerSpecificDenseExecution.multiply p q).2.length≤recursiveLength N*(p.length+1) := by
  induction p with
  | nil =>
    simp only [PlayerSpecificDenseExecution.multiply,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil]
    unfold recursiveLength
    nlinarith
  | cons a p ih =>
    have hpl : p.length≤N := by simp only [List.length_cons] at hp; omega
    have ht := ih hpl
    have hs := PlayerSpecificDenseTraceLength.scale_length a q N hq
    have hsv : (PlayerSpecificDenseExecution.scale a q).1.length=q.length := by
      rw [PlayerSpecificDenseExecution.scale_value,PlayerSpecificDensePolynomial.scale_length]
    have htv : (PlayerSpecificDenseExecution.multiply p q).1.length≤2*N := by
      rw [PlayerSpecificDenseExecution.multiply_value]
      exact (PlayerSpecificDensePolynomial.multiply_length p q).trans (by omega)
    have hshift : (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.multiply p q).1).1.length≤2*N+1 := by
      rw [PlayerSpecificDenseExecution.shift_value]
      change (PlayerSpecificDenseExecution.multiply p q).1.length+1≤_
      omega
    have ha := PlayerSpecificDenseTraceLength.add_length (PlayerSpecificDenseExecution.scale a q).1
      (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.multiply p q).1).1 (2*N+2)
      (by omega) (by omega)
    have hav : (PlayerSpecificDenseExecution.add (PlayerSpecificDenseExecution.scale a q).1
        (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.multiply p q).1).1).1.length≤2*N+1 := by
      rw [PlayerSpecificDenseExecution.add_value,PlayerSpecificDensePolynomial.add_length]
      exact max_le (by omega) hshift
    have hsm := Nat.mul_le_mul_left (N+8) (Nat.add_le_add_right hq 1)
    have ham := Nat.mul_le_mul_left (2*N+2+10) (show (PlayerSpecificDenseExecution.scale a q).1.length+
        (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.multiply p q).1).1.length+1≤3*N+2 by omega)
    simp only [PlayerSpecificDenseExecution.multiply,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil,PlayerSpecificDenseTraceLength.shift_length]
    unfold recursiveLength at ht ⊢
    nlinarith

theorem derivative_length (p : Data) (N : ℕ) (hp : p.length≤N) :
    (PlayerSpecificDenseExecution.derivative p).2.length≤recursiveLength N*(p.length+1) := by
  induction p with
  | nil =>
    simp only [PlayerSpecificDenseExecution.derivative,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil]
    unfold recursiveLength
    nlinarith
  | cons a p ih =>
    have hpl : p.length≤N := by simp only [List.length_cons] at hp; omega
    have ht := ih hpl
    have htv : (PlayerSpecificDenseExecution.derivative p).1.length≤N := by
      rw [PlayerSpecificDenseExecution.derivative_value]
      exact (PlayerSpecificDensePolynomial.derivative_length p).trans hpl
    have hshift : (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.derivative p).1).1.length≤N+1 := by
      rw [PlayerSpecificDenseExecution.shift_value]
      change (PlayerSpecificDenseExecution.derivative p).1.length+1≤_
      omega
    have ha := PlayerSpecificDenseTraceLength.add_length p
      (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.derivative p).1).1 (N+1) (by omega) hshift
    have hav : (PlayerSpecificDenseExecution.add p
        (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.derivative p).1).1).1.length≤N+1 := by
      rw [PlayerSpecificDenseExecution.add_value,PlayerSpecificDensePolynomial.add_length]
      exact max_le (by omega) hshift
    have ham := Nat.mul_le_mul_left (N+1+10) (show p.length+
        (PlayerSpecificDenseExecution.shift (PlayerSpecificDenseExecution.derivative p).1).1.length+1≤2*N+2 by omega)
    simp only [PlayerSpecificDenseExecution.derivative,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil,PlayerSpecificDenseTraceLength.shift_length]
    unfold recursiveLength at ht ⊢
    nlinarith

end Blotto.PlayerSpecificCompositeTraceLength
