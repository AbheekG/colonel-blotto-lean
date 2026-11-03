import Blotto.GeneralPaperEqualRealSegmentFactory

/-! Unit-cost length construction and fused next-fit packing. Constructed
integer weights are available scalar cells; no original encoding is scanned.
Member reversal and conversion to the small group array are explicitly priced. -/
namespace Blotto.GeneralPaperEqualRealPrefix
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

def lengths {n : ℕ} (weights : FixedArrayTable n ℕ) (D : ℕ) : FixedArrayTable n ℚ × ℕ :=
  let denominator : ℚ := D
  let actual := PaperIndexedArrayConstruction.run (fun _ => 1) 1
    (fun j => (2 * ((weights.read j : ℚ) / denominator), 16))
  (actual.1, actual.2 + 16)

theorem lengths_data {n : ℕ} (weights : FixedArrayTable n ℕ) (D : ℕ) :
    (lengths weights D).1 = FixedArrayTable.ofFn (fun j => 2 * ((weights.read j : ℚ) / D)) := by
  exact PaperIndexedArrayConstruction.run_data _ _ _

theorem lengths_work {n : ℕ} (weights : FixedArrayTable n ℕ) (D : ℕ) :
    (lengths weights D).2 ≤ 58 * n + 34 := by
  have h := GeneralPaperRealSegmentCompiler.array_work
    (fun j => (2 * ((weights.read j : ℚ) / D), 16)) 16 (fun _ => le_rfl)
  unfold lengths
  dsimp only
  omega

def reverse {α : Type*} : List α → List α → List α × ℕ
  | [], acc => (acc, 4)
  | x :: rest, acc => let child := reverse rest (x :: acc); (child.1, child.2 + 8)

theorem reverse_data {α : Type*} (xs acc : List α) : (reverse xs acc).1 = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simpa only [reverse, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, List.singleton_append] using ih (x :: acc)

theorem reverse_work {α : Type*} (xs acc : List α) : (reverse xs acc).2 = 8 * xs.length + 4 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [reverse, ih, List.length_cons]; omega

def scan {n : ℕ} (values : FixedArrayTable n ℚ) (B : ℚ) :
    List (Fin n) → ℚ → List (Fin n) → List (List (Fin n) × ℚ) × ℕ
  | current, s, [] =>
    let members := reverse current []
    ([(members.1, s)], members.2 + 8)
  | current, s, x :: rest =>
    let value := values.read x
    let next := s + value
    if next ≤ B then
      let child := scan values B (x :: current) next rest
      (child.1, child.2 + 16)
    else
      let members := reverse current []
      let child := scan values B [x] value rest
      ((members.1, s) :: child.1, members.2 + child.2 + 16)

theorem scan_data {n : ℕ} (values : FixedArrayTable n ℚ) (B : ℚ)
    (current : List (Fin n)) (s : ℚ) (rest : List (Fin n)) :
    (scan values B current s rest).1 = rationalPackSumsAux values.read B current s rest := by
  induction rest generalizing current s with
  | nil => simp only [scan, reverse_data, List.append_nil, rationalPackSumsAux]
  | cons x rest ih =>
    rw [scan, rationalPackSumsAux]
    dsimp only
    split_ifs
    · exact ih _ _
    · rw [ih, reverse_data, List.append_nil]

theorem scan_work {n : ℕ} (values : FixedArrayTable n ℚ) (B : ℚ)
    (current : List (Fin n)) (s : ℚ) (rest : List (Fin n)) :
    (scan values B current s rest).2 ≤ 32 * rest.length + 8 * current.length + 16 := by
  induction rest generalizing current s with
  | nil => simp only [scan, reverse_work, List.length_nil]; omega
  | cons x rest ih =>
    rw [scan]
    dsimp only
    split
    · have h := ih (x :: current) (s + values.read x)
      simp only [List.length_cons] at h ⊢
      omega
    · have h := ih [x] (values.read x)
      rw [reverse_work]
      simp only [List.length_cons, List.length_nil] at h ⊢
      omega

def packed {n : ℕ} (values : FixedArrayTable n ℚ) (B : ℚ) : List (Fin n) → List (List (Fin n) × ℚ) × ℕ
  | [] => ([], 8)
  | x :: rest => let child := scan values B [x] (values.read x) rest; (child.1, child.2 + 16)

theorem packed_data {n : ℕ} (values : FixedArrayTable n ℚ) (B : ℚ) (items : List (Fin n)) :
    (packed values B items).1 = rationalPackedGroups values.read B items := by
  cases items with
  | nil => rfl
  | cons x rest => exact scan_data values B [x] (values.read x) rest

theorem packed_work {n : ℕ} (values : FixedArrayTable n ℚ) (B : ℚ) (items : List (Fin n)) :
    (packed values B items).2 ≤ 32 * items.length + 32 := by
  cases items with
  | nil => simp only [packed, List.length_nil]; omega
  | cons x rest =>
    have h := scan_work values B [x] (values.read x) rest
    simp only [packed, List.length_cons, List.length_nil] at h ⊢
    omega

def prepare {n : ℕ} (i : RationalTerminalLotto n) (values : FixedArrayTable n ℚ)
    (hv : ∀ j, values.read j = i.length j) (items : List (Fin n)) (hi : items = i.uniformItems) : RationalTerminalPacking i × ℕ :=
  let actual := packed values i.B items
  let h : actual.1 = rationalPackedGroups i.length i.B i.uniformItems := by rw [packed_data, funext hv, hi]
  (GeneralPaperEqualMaterializedPacking.ofRows i actual.1 h, actual.2 + 8 * actual.1.length + 16)

theorem prepare_data {n : ℕ} (i : RationalTerminalLotto n) (values : FixedArrayTable n ℚ)
    (hv : ∀ j, values.read j = i.length j) (items : List (Fin n)) (hi : items = i.uniformItems) :
    (prepare i values hv items hi).1 = RationalTerminalPacking.prepare i := by
  unfold prepare
  dsimp only
  exact GeneralPaperEqualMaterializedPacking.ofRows_eq _ _ _

theorem prepare_work {n : ℕ} (i : RationalTerminalLotto n) (values : FixedArrayTable n ℚ)
    (hv : ∀ j, values.read j = i.length j) (items : List (Fin n)) (hi : items = i.uniformItems) :
    (prepare i values hv items hi).2 ≤ 128 * (n + 1) := by
  have h := packed_work values i.B items
  have hCount : (packed values i.B items).1.length ≤ 3 := by
    rw [packed_data, funext hv, hi]
    have hg := congrArg List.length (rationalPackedGroups_groups i.length i.B i.uniformItems)
    simp only [List.length_map] at hg
    change (rationalPackedGroups i.length i.B i.uniformItems).length = i.groups.length at hg
    rw [hg]
    rcases i.groups_count with h | h <;> omega
  have hLength : items.length ≤ n := by
    rw [hi]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  dsimp only [prepare]
  omega

end Blotto.GeneralPaperEqualRealPrefix
