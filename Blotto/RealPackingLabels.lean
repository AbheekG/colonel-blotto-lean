import Blotto.RealPackedGroups
import Blotto.TerminalLottoGrouping

/-! Labels for the actual cached-sum scan: one length read, addition,
comparison and member cons per remaining item; one reversal visit per member;
one emitted group cell per stored group. Counter/allocator/backend costs are
outside these labels and remain part of the full cost-model obligation. -/

namespace Blotto
open scoped Classical

structure RealPackingLabels where
  reads : ℕ
  additions : ℕ
  comparisons : ℕ
  memberCons : ℕ
  reversalCells : ℕ
  groupCells : ℕ

def RealPackingLabels.work (w : RealPackingLabels) : ℕ :=
  w.reads + w.additions + w.comparisons + w.memberCons + w.reversalCells + w.groupCells

noncomputable def realPackSumsLabels {α : Type*} (L : α → ℝ) (B : ℝ) :
    List α → ℝ → List α → RealPackingLabels
  | current, _, [] => ⟨0, 0, 0, 0, current.length, 1⟩
  | current, s, x :: rest =>
    let itemLength := L x
    let next := s + itemLength
    if next ≤ B then
      let w := realPackSumsLabels L B (x :: current) next rest
      ⟨w.reads + 1, w.additions + 1, w.comparisons + 1, w.memberCons + 1, w.reversalCells, w.groupCells⟩
    else
      let w := realPackSumsLabels L B [x] itemLength rest
      ⟨w.reads + 1, w.additions + 1, w.comparisons + 1, w.memberCons + 1,
        current.length + w.reversalCells, w.groupCells + 1⟩

theorem realPackSumsLabels_fields {α : Type*} (L : α → ℝ) (B : ℝ)
    (current : List α) (s : ℝ) (rest : List α) :
    (realPackSumsLabels L B current s rest).reads = rest.length ∧
      (realPackSumsLabels L B current s rest).additions = rest.length ∧
      (realPackSumsLabels L B current s rest).comparisons = rest.length ∧
      (realPackSumsLabels L B current s rest).memberCons = rest.length := by
  induction rest generalizing current s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons x rest ih =>
    rw [realPackSumsLabels]
    split_ifs
    · have h := ih (x :: current) (s + L x)
      exact ⟨congrArg (fun n => n + 1) h.1, congrArg (fun n => n + 1) h.2.1,
        congrArg (fun n => n + 1) h.2.2.1, congrArg (fun n => n + 1) h.2.2.2⟩
    · have h := ih [x] (L x)
      exact ⟨congrArg (fun n => n + 1) h.1, congrArg (fun n => n + 1) h.2.1,
        congrArg (fun n => n + 1) h.2.2.1, congrArg (fun n => n + 1) h.2.2.2⟩

theorem realPackSumsLabels_reversal {α : Type*} (L : α → ℝ) (B : ℝ)
    (current : List α) (s : ℝ) (rest : List α) :
    (realPackSumsLabels L B current s rest).reversalCells = current.length + rest.length := by
  induction rest generalizing current s with
  | nil => simp [realPackSumsLabels]
  | cons x rest ih =>
    rw [realPackSumsLabels]
    split_ifs
    · change (realPackSumsLabels L B (x :: current) (s + L x) rest).reversalCells = _
      rw [ih]
      simp only [List.length_cons]
      omega
    · change current.length + (realPackSumsLabels L B [x] (L x) rest).reversalCells = _
      rw [ih]
      simp only [List.length_cons, List.length_nil]
      omega

theorem realPackSumsLabels_groups {α : Type*} (L : α → ℝ) (B : ℝ)
    (current : List α) (s : ℝ) (rest : List α) :
    (realPackSumsLabels L B current s rest).groupCells = (realPackSumsAux L B current s rest).length := by
  induction rest generalizing current s with
  | nil => rfl
  | cons x rest ih =>
    rw [realPackSumsLabels, realPackSumsAux]
    split_ifs
    · exact ih _ _
    · change (realPackSumsLabels L B [x] (L x) rest).groupCells + 1 =
        (realPackSumsAux L B [x] (L x) rest).length + 1
      rw [ih]

noncomputable def realPackedLabels {α : Type*} (L : α → ℝ) (B : ℝ) : List α → RealPackingLabels
  | [] => ⟨0, 0, 0, 0, 0, 0⟩
  | x :: rest =>
    let w := realPackSumsLabels L B [x] (L x) rest
    ⟨w.reads + 1, w.additions, w.comparisons, w.memberCons + 1, w.reversalCells, w.groupCells⟩

theorem realPackedLabels_work {α : Type*} (L : α → ℝ) (B : ℝ) (items : List α)
    (hGroups : (realPackedGroups L B items).length ≤ 3) :
    (realPackedLabels L B items).work ≤ 5 * items.length + 1 := by
  cases items with
  | nil => simp [realPackedLabels, RealPackingLabels.work]
  | cons x rest =>
    have h := realPackSumsLabels_fields L B [x] (L x) rest
    have hRev := realPackSumsLabels_reversal L B [x] (L x) rest
    have hCount := realPackSumsLabels_groups L B [x] (L x) rest
    change (realPackSumsAux L B [x] (L x) rest).length ≤ 3 at hGroups
    change (realPackSumsLabels L B [x] (L x) rest).reads + 1 +
      (realPackSumsLabels L B [x] (L x) rest).additions +
      (realPackSumsLabels L B [x] (L x) rest).comparisons +
      ((realPackSumsLabels L B [x] (L x) rest).memberCons + 1) +
      (realPackSumsLabels L B [x] (L x) rest).reversalCells +
      (realPackSumsLabels L B [x] (L x) rest).groupCells ≤ 5 * (rest.length + 1) + 1
    simp only [List.length_cons, List.length_nil] at hRev
    omega

theorem TerminalLotto.realPacking_work {n : ℕ} (i : TerminalLotto n) :
    (realPackedLabels i.length i.B i.uniformItems).work ≤ 5 * n + 1 := by
  have hCount : (realPackedGroups i.length i.B i.uniformItems).length ≤ 3 := by
    have h := congrArg List.length (realPackedGroups_groups i.length i.B i.uniformItems)
    have hLen : (realPackedGroups i.length i.B i.uniformItems).length = i.groups.length := by
      simpa only [List.length_map, TerminalLotto.groups] using h
    rw [hLen]
    exact i.groups_count_upper
  have h := realPackedLabels_work i.length i.B i.uniformItems hCount
  have hItems : i.uniformItems.length ≤ n :=
    (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  omega

end Blotto
