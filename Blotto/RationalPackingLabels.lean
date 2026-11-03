import Blotto.RationalPackedGroups
import Blotto.RationalTerminalLotto

/-! Labels for the actual cached-sum scan: one length read, addition,
comparison and member cons per remaining item; one reversal visit per member;
one emitted group cell per stored group. Counter/allocator/backend costs are
outside these labels and remain part of the full cost-model obligation. -/

namespace Blotto
open scoped Classical

structure RationalPackingLabels where
  reads : ℕ
  additions : ℕ
  comparisons : ℕ
  memberCons : ℕ
  reversalCells : ℕ
  groupCells : ℕ

def RationalPackingLabels.work (w : RationalPackingLabels) : ℕ :=
  w.reads + w.additions + w.comparisons + w.memberCons + w.reversalCells + w.groupCells

def rationalPackSumsLabels {α : Type*} (L : α → ℚ) (B : ℚ) :
    List α → ℚ → List α → RationalPackingLabels
  | current, _, [] => ⟨0, 0, 0, 0, current.length, 1⟩
  | current, s, x :: rest =>
    let itemLength := L x
    let next := s + itemLength
    if next ≤ B then
      let w := rationalPackSumsLabels L B (x :: current) next rest
      ⟨w.reads + 1, w.additions + 1, w.comparisons + 1, w.memberCons + 1, w.reversalCells, w.groupCells⟩
    else
      let w := rationalPackSumsLabels L B [x] itemLength rest
      ⟨w.reads + 1, w.additions + 1, w.comparisons + 1, w.memberCons + 1,
        current.length + w.reversalCells, w.groupCells + 1⟩

theorem rationalPackSumsLabels_fields {α : Type*} (L : α → ℚ) (B : ℚ)
    (current : List α) (s : ℚ) (rest : List α) :
    (rationalPackSumsLabels L B current s rest).reads = rest.length ∧
      (rationalPackSumsLabels L B current s rest).additions = rest.length ∧
      (rationalPackSumsLabels L B current s rest).comparisons = rest.length ∧
      (rationalPackSumsLabels L B current s rest).memberCons = rest.length := by
  induction rest generalizing current s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons x rest ih =>
    rw [rationalPackSumsLabels]
    split_ifs
    · have h := ih (x :: current) (s + L x)
      exact ⟨congrArg (fun n => n + 1) h.1, congrArg (fun n => n + 1) h.2.1,
        congrArg (fun n => n + 1) h.2.2.1, congrArg (fun n => n + 1) h.2.2.2⟩
    · have h := ih [x] (L x)
      exact ⟨congrArg (fun n => n + 1) h.1, congrArg (fun n => n + 1) h.2.1,
        congrArg (fun n => n + 1) h.2.2.1, congrArg (fun n => n + 1) h.2.2.2⟩

theorem rationalPackSumsLabels_reversal {α : Type*} (L : α → ℚ) (B : ℚ)
    (current : List α) (s : ℚ) (rest : List α) :
    (rationalPackSumsLabels L B current s rest).reversalCells = current.length + rest.length := by
  induction rest generalizing current s with
  | nil => simp [rationalPackSumsLabels]
  | cons x rest ih =>
    rw [rationalPackSumsLabels]
    split_ifs
    · change (rationalPackSumsLabels L B (x :: current) (s + L x) rest).reversalCells = _
      rw [ih]
      simp only [List.length_cons]
      omega
    · change current.length + (rationalPackSumsLabels L B [x] (L x) rest).reversalCells = _
      rw [ih]
      simp only [List.length_cons, List.length_nil]
      omega

theorem rationalPackSumsLabels_groups {α : Type*} (L : α → ℚ) (B : ℚ)
    (current : List α) (s : ℚ) (rest : List α) :
    (rationalPackSumsLabels L B current s rest).groupCells = (rationalPackSumsAux L B current s rest).length := by
  induction rest generalizing current s with
  | nil => rfl
  | cons x rest ih =>
    rw [rationalPackSumsLabels, rationalPackSumsAux]
    split_ifs
    · exact ih _ _
    · change (rationalPackSumsLabels L B [x] (L x) rest).groupCells + 1 =
        (rationalPackSumsAux L B [x] (L x) rest).length + 1
      rw [ih]

def rationalPackedLabels {α : Type*} (L : α → ℚ) (B : ℚ) : List α → RationalPackingLabels
  | [] => ⟨0, 0, 0, 0, 0, 0⟩
  | x :: rest =>
    let w := rationalPackSumsLabels L B [x] (L x) rest
    ⟨w.reads + 1, w.additions, w.comparisons, w.memberCons + 1, w.reversalCells, w.groupCells⟩

theorem rationalPackedLabels_work {α : Type*} (L : α → ℚ) (B : ℚ) (items : List α)
    (hGroups : (rationalPackedGroups L B items).length ≤ 3) :
    (rationalPackedLabels L B items).work ≤ 5 * items.length + 1 := by
  cases items with
  | nil => simp [rationalPackedLabels, RationalPackingLabels.work]
  | cons x rest =>
    have h := rationalPackSumsLabels_fields L B [x] (L x) rest
    have hRev := rationalPackSumsLabels_reversal L B [x] (L x) rest
    have hCount := rationalPackSumsLabels_groups L B [x] (L x) rest
    change (rationalPackSumsAux L B [x] (L x) rest).length ≤ 3 at hGroups
    change (rationalPackSumsLabels L B [x] (L x) rest).reads + 1 +
      (rationalPackSumsLabels L B [x] (L x) rest).additions +
      (rationalPackSumsLabels L B [x] (L x) rest).comparisons +
      ((rationalPackSumsLabels L B [x] (L x) rest).memberCons + 1) +
      (rationalPackSumsLabels L B [x] (L x) rest).reversalCells +
      (rationalPackSumsLabels L B [x] (L x) rest).groupCells ≤ 5 * (rest.length + 1) + 1
    simp only [List.length_cons, List.length_nil] at hRev
    omega

theorem RationalTerminalLotto.rationalPacking_work {n : ℕ} (i : RationalTerminalLotto n) :
    (rationalPackedLabels i.length i.B i.uniformItems).work ≤ 5 * n + 1 := by
  have hCount : (rationalPackedGroups i.length i.B i.uniformItems).length ≤ 3 := by
    have h := congrArg List.length (rationalPackedGroups_groups i.length i.B i.uniformItems)
    have hLen : (rationalPackedGroups i.length i.B i.uniformItems).length = i.groups.length := by
      simpa only [List.length_map, RationalTerminalLotto.groups] using h
    rw [hLen]
    rcases i.groups_count with h | h <;> omega
  have h := rationalPackedLabels_work i.length i.B i.uniformItems hCount
  have hItems : i.uniformItems.length ≤ n :=
    (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  omega

end Blotto
