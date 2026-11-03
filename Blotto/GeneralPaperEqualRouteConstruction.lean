import Blotto.GeneralPaperEqualRouteMembers

/-! Build all cached routes from the retained packed array. Runtime group
labels come from its stored size; every member list is consumed once. The
initial array and all group/list/index/reference control are priced. -/
namespace Blotto.GeneralPaperEqualRouteConstruction
set_option autoImplicit false
set_option maxHeartbeats 1200000

def indices {m : ℕ} (size : ℕ) (h : size = m) : List (Fin m) :=
  (List.finRange size).map (fun g => g.cast h)

theorem indices_eq {m : ℕ} (size : ℕ) (h : size = m) : indices size h = List.finRange m := by
  cases h
  simp [indices]

def indicesWork (A size : ℕ) : ℕ := 64 * (size + 1) * (A + binaryWordWidth (size + 1) + 1)

theorem patch_append {n : ℕ} {α : Type*} (table : FixedArrayTable n α) (xs ys : List (Fin n × α)) :
    table.patch (xs ++ ys) = (table.patch xs).patch ys := by
  induction xs generalizing table with
  | nil => rfl
  | cons x xs ih => exact ih (table.write x.1 x.2)

def groups {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) :
    List (Fin i.groups.length) → FixedArrayTable n (GroupRoute i.groups.length) → FixedArrayTable n (GroupRoute i.groups.length) × ℕ
  | [], table => (table, 32 * A + 32)
  | g :: rest, table =>
      let entry := p.groups.read g
      let made := GeneralPaperEqualRouteMembers.run model A values g entry.2 entry.1 table
      let child := groups p model A values rest made.1
      (child.1, made.2 + child.2 + 64 * (A + binaryWordWidth (g.val + 1) + 1))

theorem groups_data {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (gs : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length)) :
    (groups p model A values gs table).1 = table.patch
      (gs.flatMap (fun g => (p.groups.read g).1.map (fun j => (j, (some g, values.read j / (p.groups.read g).2))))) := by
  induction gs generalizing table with
  | nil => rfl
  | cons g gs ih =>
    rw [groups]
    dsimp only
    rw [ih, GeneralPaperEqualRouteMembers.data]
    exact (patch_append _ _ _).symm

def memberCount {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (gs : List (Fin i.groups.length)) : ℕ := (gs.flatMap (fun g => (p.groups.read g).1)).length

def groupHeader (A m : ℕ) : ℕ := 128 * (A + binaryWordWidth (m + 1) + 1)

theorem groups_work {n s : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (gs : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length))
    (hv : ∀ j, RationalHeight (values.read j) s) (ht : ∀ g, RationalHeight (p.groups.read g).2 s) :
    (groups p model A values gs table).2 ≤
      memberCount p gs * GeneralPaperEqualRouteMembers.stepBound model A n i.groups.length s +
        gs.length * groupHeader A i.groups.length + 32 * A + 32 := by
  induction gs generalizing table with
  | nil => simp only [groups, memberCount, List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons g gs ih =>
    have hm := GeneralPaperEqualRouteMembers.work model A values g (p.groups.read g).2 (p.groups.read g).1 table hv (ht g)
    have hc := ih (GeneralPaperEqualRouteMembers.run model A values g (p.groups.read g).2 (p.groups.read g).1 table).1
    have hg := binaryWordWidth_mono (show g.val + 1 ≤ i.groups.length + 1 by omega)
    rw [groups]
    dsimp only
    simp only [memberCount, List.flatMap_cons, List.length_append, List.length_cons] at hc ⊢
    unfold groupHeader at hc ⊢
    nlinarith only [hm, hc, hg]

def run {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) :
    FixedArrayTable n (GroupRoute i.groups.length) × ℕ :=
  let initial : FixedArrayTable n (GroupRoute i.groups.length) × ℕ := GeneralPaperSizedBitArray.run values.data.size values.size A
    (fun _ : Fin n => ((none, (0 : ℚ)), 32 * A + 32))
  let made := groups p model A values (indices p.groups.data.size p.groups.size) initial.1
  (made.1, initial.2 + indicesWork A p.groups.data.size + made.2 + 64 * A + 64)

theorem data {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (hv : ∀ j, values.read j = i.length j) :
    (run p model A values).1 = p.prepareOutput.table := by
  unfold run
  dsimp only
  rw [groups_data, indices_eq, GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data, funext hv]
  rfl

theorem members_eq_uniform {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    (List.finRange i.groups.length).flatMap (fun g => (p.groups.read g).1) = i.uniformItems := by
  have h := p.routeAssignments_keys_eq
  simpa only [RationalTerminalPacking.routeAssignments, List.map_flatMap, List.map_map,
    Function.comp_def, List.map_id'] using h

def bound (model : RationalCostModel) (A n m s : ℕ) : ℕ :=
  n * GeneralPaperEqualRouteMembers.stepBound model A n m s + 3 * groupHeader A m + indicesWork A m +
    32 * n * (A + 1) + 96 * (A + 1) + PaperIndexedArrayConstruction.overhead id A n n

theorem work {n s : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (hv : ∀ j, RationalHeight (values.read j) s) (ht : ∀ g, RationalHeight (p.groups.read g).2 s) :
    (run p model A values).2 ≤ bound model A n i.groups.length s := by
  let initial : FixedArrayTable n (GroupRoute i.groups.length) × ℕ := GeneralPaperSizedBitArray.run values.data.size values.size A
    (fun _ : Fin n => ((none, (0 : ℚ)), 32 * A + 32))
  have hInit : initial.2 = n * (32 * A + 32) + PaperIndexedArrayConstruction.overhead id A n n := by
    dsimp only [initial]
    rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_work]
    simp
    rfl
  have hGroup := groups_work p model A values (indices p.groups.data.size p.groups.size) initial.1 hv ht
  rw [indices_eq, List.length_finRange] at hGroup
  have hMem : memberCount p (List.finRange i.groups.length) ≤ n := by
    unfold memberCount
    rw [members_eq_uniform]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  have hM := Nat.mul_le_mul_right (GeneralPaperEqualRouteMembers.stepBound model A n i.groups.length s) hMem
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  have hG := Nat.mul_le_mul_right (groupHeader A i.groups.length) hCount
  unfold run bound
  dsimp only
  change initial.2 + indicesWork A p.groups.data.size +
    (groups p model A values (indices p.groups.data.size p.groups.size) initial.1).2 + 64 * A + 64 ≤ _
  rw [hInit, indices_eq, p.groups.size]
  nlinarith only [hGroup, hM, hG]

def prepare {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (hv : ∀ j, values.read j = i.length j) :
    PreparedGroupOutput i.partition × ℕ :=
  let made := run p model A values
  (⟨made.1, by intro j; rw [data p model A values hv]; exact p.prepareOutput.correct j⟩, made.2)

theorem prepared_eq {n m : ℕ} {G : RationalProportionalGroups n m} (a b : PreparedGroupOutput G)
    (h : a.table = b.table) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem prepare_data {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (hv : ∀ j, values.read j = i.length j) :
    (prepare p model A values hv).1 = p.prepareOutput :=
  prepared_eq _ _ (data p model A values hv)

end Blotto.GeneralPaperEqualRouteConstruction
