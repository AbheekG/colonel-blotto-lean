import Blotto.GeneralPaperActualOccurrencePreparation

/-! One reference-copy traversal of the left list. The right suffix is
borrowed unchanged; the price is accumulated during the same traversal.
-/
namespace Blotto.GeneralPaperPricedListAppend
set_option autoImplicit false

def run {α : Type*} (W : ℕ) : List α → List α → List α × ℕ
  | [],ys => (ys,2*W)
  | x::xs,ys => let later := run W xs ys; (x::later.1,later.2+8*W)

theorem data {α : Type*} (W : ℕ) (xs ys : List α) : (run W xs ys).1=xs++ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [run,List.cons_append,ih]

theorem work {α : Type*} (W : ℕ) (xs ys : List α) : (run W xs ys).2=8*W*xs.length+2*W := by
  induction xs with
  | nil => simp only [run,List.length_nil,Nat.mul_zero,Nat.zero_add]
  | cons x xs ih =>
    change (run W xs ys).2+8*W=_
    rw [ih,List.length_cons]
    ring

end Blotto.GeneralPaperPricedListAppend
