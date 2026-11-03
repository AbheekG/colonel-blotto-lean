import Blotto.GeneralPaperEqualRealPrefix

/-! One real division and selected-entry route write per member. The group
array and materialized lengths are shared; no label or encoding scan occurs. -/
namespace Blotto.GeneralPaperEqualRealRoutes
open GeneralPaperEqualRouteConstruction (indices indices_eq patch_append)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def members {n m : ℕ} (values : FixedArrayTable n ℚ) (g : Fin m) (total : ℚ) :
    List (Fin n) → FixedArrayTable n (GroupRoute m) → FixedArrayTable n (GroupRoute m) × ℕ
  | [], table => (table, 8)
  | j :: rest, table =>
    let coefficient := values.read j / total
    let child := members values g total rest (table.write j (some g, coefficient))
    (child.1, child.2 + 16)

theorem members_data {n m : ℕ} (values : FixedArrayTable n ℚ) (g : Fin m) (total : ℚ)
    (items : List (Fin n)) (table : FixedArrayTable n (GroupRoute m)) :
    (members values g total items table).1 = table.patch (items.map (fun j => (j, (some g, values.read j / total)))) := by
  induction items generalizing table with
  | nil => rfl
  | cons j rest ih => exact ih _

theorem members_work {n m : ℕ} (values : FixedArrayTable n ℚ) (g : Fin m) (total : ℚ)
    (items : List (Fin n)) (table : FixedArrayTable n (GroupRoute m)) :
    (members values g total items table).2 = 16 * items.length + 8 := by
  induction items generalizing table with
  | nil => rfl
  | cons j rest ih => simp only [members, ih, List.length_cons]; omega

def groups {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) (values : FixedArrayTable n ℚ) :
    List (Fin i.groups.length) → FixedArrayTable n (GroupRoute i.groups.length) →
      FixedArrayTable n (GroupRoute i.groups.length) × ℕ
  | [], table => (table, 8)
  | g :: rest, table =>
    let entry := p.groups.read g
    let made := members values g entry.2 entry.1 table
    let child := groups p values rest made.1
    (child.1, made.2 + child.2 + 16)

theorem groups_data {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (values : FixedArrayTable n ℚ) (gs : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length)) :
    (groups p values gs table).1 = table.patch
      (gs.flatMap (fun g => (p.groups.read g).1.map (fun j => (j, (some g, values.read j / (p.groups.read g).2))))) := by
  induction gs generalizing table with
  | nil => rfl
  | cons g rest ih =>
    rw [groups]
    dsimp only
    rw [ih, members_data]
    exact (patch_append _ _ _).symm

theorem groups_work {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (values : FixedArrayTable n ℚ) (gs : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length)) :
    (groups p values gs table).2 = 16 * (gs.flatMap (fun g => (p.groups.read g).1)).length + 24 * gs.length + 8 := by
  induction gs generalizing table with
  | nil => rfl
  | cons g rest ih =>
    simp only [groups, ih, members_work, List.flatMap_cons, List.length_append, List.length_cons]
    omega

def run {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) (values : FixedArrayTable n ℚ) :=
  let initial := PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun _ : Fin n => (((none, (0 : ℚ)) : GroupRoute i.groups.length), 8))
  let made := groups p values (indices p.groups.data.size p.groups.size) initial.1
  (made.1, initial.2 + 8 * (p.groups.data.size + 1) + made.2 + 16)

theorem data {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (values : FixedArrayTable n ℚ) (hv : ∀ j, values.read j = i.length j) : (run p values).1 = p.prepareOutput.table := by
  have h := GeneralPaperEqualRouteConstruction.data p RationalCostModel.schoolbook 1 values hv
  simp only [GeneralPaperEqualRouteConstruction.run, GeneralPaperEqualRouteConstruction.groups_data,
    GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data, indices_eq] at h
  simpa only [run, groups_data, PaperIndexedArrayConstruction.run_data, indices_eq] using h

theorem work {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) (values : FixedArrayTable n ℚ) :
    (run p values).2 ≤ 256 * (n + 1) := by
  have hInit := GeneralPaperRealSegmentCompiler.array_work
    (fun _ : Fin n => (((none, (0 : ℚ)) : GroupRoute i.groups.length), 8)) 8 (fun _ => le_rfl)
  have hg := groups_work p values (indices p.groups.data.size p.groups.size)
    (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun _ : Fin n => (((none, (0 : ℚ)) : GroupRoute i.groups.length), 8))).1
  rw [indices_eq, GeneralPaperEqualRouteConstruction.members_eq_uniform, List.length_finRange] at hg
  have hm : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  have hn : i.uniformItems.length ≤ n := (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  dsimp only [run]
  rw [indices_eq, p.groups.size]
  omega

def prepare {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (values : FixedArrayTable n ℚ) (hv : ∀ j, values.read j = i.length j) : PreparedGroupOutput i.partition × ℕ :=
  let actual := run p values
  (⟨actual.1, by intro j; rw [data p values hv]; exact p.prepareOutput.correct j⟩, actual.2)

end Blotto.GeneralPaperEqualRealRoutes
