import Blotto.GeneralPaperBasisRowSize

/-! Every native integer dot product and every accumulator prefix has a
size bound. Exact arithmetic is bounded before rational reduction, rather
than relying only on a short final output.
-/
namespace Blotto.GeneralPaperIntegerDotSize
open GeneralPaperBasisIntegerDot
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem loop_bound {i : Type*} (f g : i → ℤ) (xs : List i) (a : ℤ) (spent A U : ℕ)
    (hf : ∀ x∈xs,(f x).natAbs≤A) (hg : ∀ x∈xs,(g x).natAbs≤U) :
    (loop f g xs a spent).value.natAbs≤a.natAbs+xs.length*A*U := by
  induction xs generalizing a spent with
  | nil => simp only [loop,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons x rest ih =>
    have hm : (f x*g x).natAbs≤A*U := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hf x (List.mem_cons_self)) (hg x (List.mem_cons_self))
    have ha : (a+f x*g x).natAbs≤a.natAbs+A*U :=
      (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left hm _)
    have hh := ih (a+f x*g x) (spent+12)
      (fun y hy => hf y (List.mem_cons_of_mem x hy)) (fun y hy => hg y (List.mem_cons_of_mem x hy))
    change (loop f g rest (a+f x*g x) (spent+12)).value.natAbs≤_
    apply hh.trans
    rw [List.length_cons]
    nlinarith only [ha]

theorem prefix_bound {i : Type*} (f g : i → ℤ) (xs : List i) (a : ℤ) (spent A U t : ℕ)
    (hf : ∀ x∈xs,(f x).natAbs≤A) (hg : ∀ x∈xs,(g x).natAbs≤U) :
    (loop f g (xs.take t) a spent).value.natAbs≤a.natAbs+xs.length*A*U := by
  have hh := loop_bound f g (xs.take t) a spent A U
    (fun x hx => hf x (List.mem_of_mem_take hx)) (fun x hx => hg x (List.mem_of_mem_take hx))
  have hl : (xs.take t).length≤xs.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_right U (Nat.mul_le_mul_right A hl)) _)

theorem run_bound {n : ℕ} (f g : Fin n → ℤ) (A U : ℕ)
    (hf : ∀ x,(f x).natAbs≤A) (hg : ∀ x,(g x).natAbs≤U) :
    (run f g).value.natAbs≤n*A*U := by
  have hh := loop_bound f g (List.finRange n) 0 0 A U (fun x _ => hf x) (fun x _ => hg x)
  simpa only [run,Int.natAbs_zero,Nat.zero_add,List.length_finRange] using hh

end Blotto.GeneralPaperIntegerDotSize
