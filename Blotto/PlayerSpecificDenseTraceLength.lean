import Blotto.PlayerSpecificRootTraversalContract

/-! Polynomial trace lengths for the actual dense elementary operations,
including full returned-list copies. No source-operation count is supplied. -/
namespace Blotto.PlayerSpecificDenseTraceLength
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem add_length (p q : Data) (N : ℕ) (hp : p.length≤N) (hq : q.length≤N) :
    (PlayerSpecificDenseExecution.add p q).2.length≤(N+10)*(p.length+q.length+1) := by
  induction p generalizing q with
  | nil =>
    simp only [PlayerSpecificDenseExecution.add,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil]
    nlinarith
  | cons a p ih =>
    cases q with
    | nil =>
      simp only [PlayerSpecificDenseExecution.add,PlayerSpecificDenseExecution.finish,List.length_append,
        copyRow_length,List.length_cons,List.length_nil] at hp ⊢
      nlinarith
    | cons b q =>
      have ht := ih q (by simp only [List.length_cons] at hp; omega) (by simp only [List.length_cons] at hq; omega)
      have hv : (PlayerSpecificDenseExecution.add p q).1.length≤N := by
        rw [PlayerSpecificDenseExecution.add_value,PlayerSpecificDensePolynomial.add_length]
        apply max_le <;> simp only [List.length_cons] at hp hq <;> omega
      simp only [PlayerSpecificDenseExecution.add,PlayerSpecificDenseExecution.finish,List.length_append,
        copyRow_length,List.length_cons,List.length_nil,scalar_length]
      nlinarith

theorem scale_length (a : ℚ) (p : Data) (N : ℕ) (hp : p.length≤N) :
    (PlayerSpecificDenseExecution.scale a p).2.length≤(N+8)*(p.length+1) := by
  induction p with
  | nil =>
    simp only [PlayerSpecificDenseExecution.scale,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil]
    nlinarith
  | cons b p ih =>
    have ht := ih (by simp only [List.length_cons] at hp; omega)
    have hv : (PlayerSpecificDenseExecution.scale a p).1.length=p.length := by
      rw [PlayerSpecificDenseExecution.scale_value,PlayerSpecificDensePolynomial.scale_length]
    simp only [PlayerSpecificDenseExecution.scale,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil,scalar_length,hv]
    simp only [List.length_cons] at hp
    nlinarith

theorem shift_length (p : Data) : (PlayerSpecificDenseExecution.shift p).2.length=2*p.length+5 := by
  simp only [PlayerSpecificDenseExecution.shift,PlayerSpecificDenseExecution.finish,List.length_append,
    copyRow_length,List.length_cons,List.length_nil]
  omega

theorem trim_length (p : Data) (N : ℕ) (hp : p.length≤N) :
    (PlayerSpecificDenseExecution.trim p).2.length≤(N+8)*(p.length+1) := by
  induction p with
  | nil =>
    simp only [PlayerSpecificDenseExecution.trim,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil]
    nlinarith
  | cons a p ih =>
    have ht := ih (by simp only [List.length_cons] at hp; omega)
    have hv : (PlayerSpecificDenseExecution.trim p).1.length≤p.length := by
      rw [PlayerSpecificDenseExecution.trim_value]
      exact PlayerSpecificDensePolynomial.trim_length p
    simp only [PlayerSpecificDenseExecution.trim,PlayerSpecificDenseExecution.finish,List.length_append,
      copyRow_length,List.length_cons,List.length_nil,equalZero_length]
    split_ifs <;> simp only [List.length_cons,List.length_nil] at hp ⊢ <;> nlinarith

end Blotto.PlayerSpecificDenseTraceLength
