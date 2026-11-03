import Blotto.GeneralPaperOrderedScatterPrice

/-! Unconditional unit prices for native streaming scatter. Rational
magnitudes and table validity are not needed in this interpretation. -/
namespace Blotto.GeneralPaperOrderedScatterArithmetic
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem insert_work {Witness : Type*} {J : ℕ} (table : Table Tag Witness J) (entry : Entry Tag Witness J) :
    (GeneralPaperOrderedScatterExecution.insert (fun _ => 1) 1 1 table entry).2≤258 := by
  have h := GeneralPaperOrderedMinimumPrice.arithmetic_work (table.read entry.label) (some entry.selection)
  change (GeneralPaperOrderedMinimumPrice.run (fun _ => 1) 1 (table.read entry.label) (some entry.selection)).2+128≤258
  omega

theorem apply_work {Witness : Type*} {J : ℕ} (table : Table Tag Witness J) (entry : Option (Entry Tag Witness J)) :
    (GeneralPaperOrderedScatterExecution.applyEntry (fun _ => 1) 1 1 table entry).2≤322 := by
  cases entry with
  | none => change 64≤322; omega
  | some e =>
    have h := insert_work table e
    change (GeneralPaperOrderedScatterExecution.insert (fun _ => 1) 1 1 table e).2+64≤322
    omega

theorem fold_work {α Witness : Type*} {J : ℕ} (C : ℕ) (evaluate : α → Option (Entry Tag Witness J) × ℕ)
    (xs : List α) (table : Table Tag Witness J) (hc : ∀ a∈xs,(evaluate a).2≤C) :
    (GeneralPaperOrderedScatterExecution.fold (fun _ => 1) 1 1 evaluate xs table).2≤xs.length*(C+386)+64 := by
  induction xs generalizing table with
  | nil => change 64≤0*(C+386)+64; omega
  | cons a rest ih =>
    have ha := hc a List.mem_cons_self
    have hu := apply_work table (evaluate a).1
    have hr := ih (GeneralPaperOrderedScatterExecution.applyEntry (fun _ => 1) 1 1 table (evaluate a).1).1
      (fun b hb => hc b (List.mem_cons_of_mem _ hb))
    change (evaluate a).2+(GeneralPaperOrderedScatterExecution.applyEntry (fun _ => 1) 1 1 table (evaluate a).1).2+
      (GeneralPaperOrderedScatterExecution.fold (fun _ => 1) 1 1 evaluate rest
        (GeneralPaperOrderedScatterExecution.applyEntry (fun _ => 1) 1 1 table (evaluate a).1).1).2+64≤_
    rw [List.length_cons]
    nlinarith only [ha,hu,hr]

theorem rows_work {α β Witness : Type*} {J : ℕ} (C : ℕ) (evaluate : α → β → Option (Entry Tag Witness J) × ℕ)
    (columns : List β) (xs : List α) (table : Table Tag Witness J) (hc : ∀ a∈xs,∀ b∈columns,(evaluate a b).2≤C) :
    (GeneralPaperOrderedScatterExecution.rows (fun _ => 1) 1 1 evaluate columns xs table).2≤
      xs.length*(columns.length*(C+386)+128)+64 := by
  induction xs generalizing table with
  | nil => change 64≤0*(columns.length*(C+386)+128)+64; omega
  | cons a rest ih =>
    have hf := fold_work C (evaluate a) columns table (hc a List.mem_cons_self)
    have hr := ih (GeneralPaperOrderedScatterExecution.fold (fun _ => 1) 1 1 (evaluate a) columns table).1
      (fun b hb => hc b (List.mem_cons_of_mem _ hb))
    change (GeneralPaperOrderedScatterExecution.fold (fun _ => 1) 1 1 (evaluate a) columns table).2+
      (GeneralPaperOrderedScatterExecution.rows (fun _ => 1) 1 1 evaluate columns rest
        (GeneralPaperOrderedScatterExecution.fold (fun _ => 1) 1 1 (evaluate a) columns table).1).2+64≤_
    rw [List.length_cons]
    nlinarith only [hf,hr]

end Blotto.GeneralPaperOrderedScatterArithmetic
