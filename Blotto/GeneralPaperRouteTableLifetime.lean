import Blotto.GeneralPaperEqualPackingCapacity

/-! Every partial selected-entry route write preserves a short rational
coefficient invariant. One mutable route backing array owns the payload;
recursive frames keep references and never duplicate whole table snapshots. -/
namespace Blotto.GeneralPaperRouteTableLifetime
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEqualRetainedStorage (routeFoot route_bound)
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Short {n m : ℕ} (s : ℕ) (table : FixedArrayTable n (GroupRoute m)) : Prop :=
  ∀ j, RationalHeight (table.read j).2 (2 * s)

def profile (A n m s : ℕ) : ℕ := arrayProfile A n (4 + binaryWordWidth m + 2 * (2 * s) + 16 * A)

theorem table_bound {n m : ℕ} (A s : ℕ) (table : FixedArrayTable n (GroupRoute m)) (h : Short s table) :
    arrayFootprint A (routeFoot A) table ≤ profile A n m s :=
  array_bound A _ (routeFoot A) table (fun j => route_bound A _ (h j))

theorem write_short {n m s : ℕ} (table : FixedArrayTable n (GroupRoute m)) (h : Short s table)
    (j : Fin n) (g : Fin m) (q : ℚ) (hq : RationalHeight q (2 * s)) :
    Short s (table.write j (some g, q)) := by
  intro i
  rw [FixedArrayTable.read_write]
  split_ifs
  · exact hq
  · exact h i

theorem member_short {n m s : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) (items : List (Fin n)) (table : FixedArrayTable n (GroupRoute m))
    (hv : ∀ j, RationalHeight (values.read j) s) (ht : RationalHeight total s) (hTable : Short s table) :
    Short s (GeneralPaperEqualRouteMembers.run model A values g total items table).1 := by
  induction items generalizing table with
  | nil => exact hTable
  | cons j rest ih =>
    have hQ : RationalHeight (GeneralPaperRationalScalarStep.run model A .div (values.read j) total).1 (2 * s) := by
      simpa only [GeneralPaperRationalScalarStep.data, GeneralPaperRationalScalarStep.Op.apply, two_mul] using (hv j).div ht
    rw [GeneralPaperEqualRouteMembers.run]
    dsimp only
    exact ih _ (write_short table hTable j g _ hQ)

theorem groups_short {n s : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (gs : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length))
    (hv : ∀ j, RationalHeight (values.read j) s) (ht : ∀ g, RationalHeight (p.groups.read g).2 s) (hTable : Short s table) :
    Short s (GeneralPaperEqualRouteConstruction.groups p model A values gs table).1 := by
  induction gs generalizing table with
  | nil => exact hTable
  | cons g rest ih =>
    rw [GeneralPaperEqualRouteConstruction.groups]
    dsimp only
    exact ih _ (member_short model A values g (p.groups.read g).2 (p.groups.read g).1 table hv (ht g) hTable)

theorem member_continuation {n m : ℕ} (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (g : Fin m) (total : ℚ) (first rest : List (Fin n)) (table : FixedArrayTable n (GroupRoute m)) :
    (GeneralPaperEqualRouteMembers.run model A values g total (first ++ rest) table).1 =
      (GeneralPaperEqualRouteMembers.run model A values g total rest
        (GeneralPaperEqualRouteMembers.run model A values g total first table).1).1 := by
  simp only [GeneralPaperEqualRouteMembers.data, List.map_append, GeneralPaperEqualRouteConstruction.patch_append]

theorem group_continuation {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ)
    (first rest : List (Fin i.groups.length)) (table : FixedArrayTable n (GroupRoute i.groups.length)) :
    (GeneralPaperEqualRouteConstruction.groups p model A values (first ++ rest) table).1 =
      (GeneralPaperEqualRouteConstruction.groups p model A values rest
        (GeneralPaperEqualRouteConstruction.groups p model A values first table).1).1 := by
  simp only [GeneralPaperEqualRouteConstruction.groups_data, List.flatMap_append, GeneralPaperEqualRouteConstruction.patch_append]

def initial {n m : ℕ} (values : FixedArrayTable n ℚ) (A : ℕ) : FixedArrayTable n (GroupRoute m) × ℕ :=
  GeneralPaperSizedBitArray.run values.data.size values.size A (fun _ : Fin n => ((none, (0 : ℚ)), 32 * A + 32))

theorem initial_short {n m s : ℕ} (values : FixedArrayTable n ℚ) (A : ℕ) (hs : 2 ≤ s) :
    Short s (initial (m := m) values A).1 := by
  intro j
  simp only [initial, GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
  exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (by omega)

end Blotto.GeneralPaperRouteTableLifetime
