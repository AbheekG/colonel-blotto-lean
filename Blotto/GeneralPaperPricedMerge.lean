import Blotto.GeneralPaperRayComparisonOperandSize

/-! Priced stable merge, with one comparator call per decision and constant
reference/control traffic. This is the paper source model, parametrized by
the declared word price W; no native allocator/library rate is asserted.
-/
namespace Blotto.GeneralPaperPricedMerge
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {α : Type*} (compare : α → α → Bool × ℕ) (W : ℕ) : List α → List α → List α × ℕ
  | [],ys => (ys,2*W)
  | xs,[] => (xs,2*W)
  | x::xs,y::ys =>
    let current := compare x y
    if current.1 then
      let child := run compare W xs (y::ys)
      (x::child.1,child.2+current.2+8*W)
    else
      let child := run compare W (x::xs) ys
      (y::child.1,child.2+current.2+8*W)
termination_by xs ys => xs.length+ys.length

theorem data {α : Type*} (compare : α → α → Bool × ℕ) (W : ℕ) (xs ys : List α) :
    (run compare W xs ys).1=List.merge xs ys (fun a b => (compare a b).1) := by
  cases xs with
  | nil => simp only [run,List.merge]
  | cons x xs =>
    cases ys with
    | nil => simp only [run,List.merge]
    | cons y ys =>
      simp only [run,List.merge]
      split
      · exact congrArg (List.cons x) (data compare W xs (y::ys))
      · exact congrArg (List.cons y) (data compare W (x::xs) ys)
termination_by xs.length+ys.length
decreasing_by all_goals simp_wf

theorem length {α : Type*} (compare : α → α → Bool × ℕ) (W : ℕ) (xs ys : List α) :
    (run compare W xs ys).1.length=xs.length+ys.length := by
  rw [data,List.length_merge]

theorem work {α : Type*} (compare : α → α → Bool × ℕ) (W P : ℕ) (xs ys : List α)
    (h : ∀ a∈xs,∀ b∈ys,(compare a b).2≤P) :
    (run compare W xs ys).2≤(P+8*W)*(xs.length+ys.length)+2*W := by
  generalize hn : xs.length+ys.length=n
  induction n using Nat.strong_induction_on generalizing xs ys with
  | h n ih =>
    cases xs with
    | nil => simp only [run]; omega
    | cons x xs =>
      cases ys with
      | nil => simp only [run]; omega
      | cons y ys =>
        have hc := h x List.mem_cons_self y List.mem_cons_self
        rw [run]
        split
        · have hh := ih (xs.length+(y::ys).length) (by simp only [List.length_cons] at hn ⊢; omega)
            xs (y::ys) (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b hb) rfl
          simp only [List.length_cons] at hh hn ⊢
          nlinarith only [hc,hh,hn]
        · have hh := ih ((x::xs).length+ys.length) (by simp only [List.length_cons] at hn ⊢; omega)
            (x::xs) ys (fun a ha b hb => h a ha b (List.mem_cons_of_mem _ hb)) rfl
          simp only [List.length_cons] at hh hn ⊢
          nlinarith only [hc,hh,hn]

end Blotto.GeneralPaperPricedMerge
