import Blotto.GeneralPaperResponseTag

/-! Literal row semantics of the symbolic response tag. The threshold sum
and any-open flag are computed separately; physical shifts are not inputs to
this resource algebra or its budget test.
-/
namespace Blotto.GeneralPaperResponseTagSums
open GeneralPaperResponseTag
set_option autoImplicit false

theorem threshold_sum (tags : List Tag) : tags.sum.threshold=(tags.map Tag.threshold).sum := by
  induction tags with
  | nil => rfl
  | cons a rest ih => simp only [List.sum_cons,threshold_add,List.map_cons,ih]

theorem opened_sum (tags : List Tag) : tags.sum.opened=tags.any Tag.opened := by
  induction tags with
  | nil => rfl
  | cons a rest ih => simp only [List.sum_cons,opened_add,List.any_cons,ih]

theorem sum_closed_iff (tags : List Tag) : tags.sum.opened=false ↔ ∀ a∈tags, a.opened=false := by
  rw [opened_sum,List.any_eq_false]
  simp only [Bool.not_eq_true]

theorem sum_feasible_iff (tags : List Tag) (B : ℚ) : tags.sum≤budget B ↔
    (tags.map Tag.threshold).sum<B ∨ ((tags.map Tag.threshold).sum=B ∧ ∀ a∈tags, a.opened=false) := by
  rw [feasible_iff,threshold_sum,sum_closed_iff]

theorem closed_add (a b : ℚ) : (⟨a,false⟩:Tag)+⟨b,false⟩=⟨a+b,false⟩ := rfl

theorem closed_sum (thresholds : List ℚ) : (thresholds.map (fun a => (⟨a,false⟩:Tag))).sum=⟨thresholds.sum,false⟩ := by
  induction thresholds with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons,List.sum_cons,ih,closed_add]

end Blotto.GeneralPaperResponseTagSums
