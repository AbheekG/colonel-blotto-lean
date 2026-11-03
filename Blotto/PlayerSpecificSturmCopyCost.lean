import Blotto.PlayerSpecificSturmExecution

/-! Complete copies of each stored Sturm row and the enclosing row list. -/
namespace Blotto.PlayerSpecificSturmCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificSturmExecution
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem copyRows_cost (model : RationalCostModel) (rows : List Data) (T W : ℕ)
    (hr : ∀ row∈rows,HasHeight row T ∧ row.length≤4) (hlen : rows.length≤5)
    (hTW : 1+2*T≤W) (hW : 32≤W) : price model (copyRows rows)≤100*model.rat W := by
  have hf : Fits W (copyRows rows) := by
    intro e he
    rcases List.mem_cons.mp he with heq | ht
    · subst e
      exact (control_width rows.length).trans (by omega)
    · rcases List.mem_flatMap.mp ht with ⟨row,hrow,hm⟩
      exact copyRow_fits W row (fun q hq => (rationalWordWidth_of_height ((hr row hrow).1 q hq)).trans hTW)
        (by have hrl:=(hr row hrow).2; omega) e hm
  have hlinear : ∀ rs : List Data,(∀ row∈rs,row.length≤4) → (rs.flatMap copyRow).length≤5*rs.length := by
    intro rs
    induction rs with
    | nil => intro _; simp only [List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.le_refl]
    | cons row rs ih =>
      intro hrows
      have hrl := hrows row List.mem_cons_self
      have ht := ih (fun q hq => hrows q (List.mem_cons_of_mem row hq))
      simp only [List.flatMap_cons,List.length_append,copyRow_length,List.length_cons]
      omega
  have hl := hlinear rows (fun row hrow => (hr row hrow).2)
  have hc := price_bound model W (by omega) _ hf
  have hcap : (copyRows rows).length≤26 := by
    simp only [copyRows,List.length_cons]
    omega
  have hm := Nat.mul_le_mul_right (3*model.rat W) hcap
  nlinarith

end Blotto.PlayerSpecificSturmCopyCost
