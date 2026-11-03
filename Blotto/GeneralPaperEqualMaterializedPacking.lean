import Blotto.GeneralPaperEqualLengthArray

/-! Repackage the fused packing return as the existing law-certified group
table. The reference constructor occurs only in erased equality proofs.
The data path uses the supplied materialized lengths and actual item list. -/
namespace Blotto.GeneralPaperEqualMaterializedPacking
set_option autoImplicit false
set_option maxHeartbeats 1000000

def ofRows {n : ℕ} (i : RationalTerminalLotto n) (rows : List (List (Fin n) × ℚ))
    (hRows : rows = rationalPackedGroups i.length i.B i.uniformItems) : RationalTerminalPacking i where
  groups := ⟨rows.toArray, by
    have h := (RationalTerminalPacking.prepare i).groups.size
    change (rationalPackedGroups i.length i.B i.uniformItems).toArray.size = i.groups.length at h
    simpa only [hRows] using h⟩
  members_correct := by
    intro g
    have h := (RationalTerminalPacking.prepare i).members_correct g
    simpa only [hRows, RationalTerminalPacking.prepare] using h
  total_correct := by
    intro g
    have h := (RationalTerminalPacking.prepare i).total_correct g
    simpa only [hRows, RationalTerminalPacking.prepare] using h

theorem ofRows_eq {n : ℕ} (i : RationalTerminalLotto n) (rows : List (List (Fin n) × ℚ))
    (hRows : rows = rationalPackedGroups i.length i.B i.uniformItems) :
    ofRows i rows hRows = RationalTerminalPacking.prepare i := by
  cases hRows
  rfl

def run {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel) (A : ℕ)
    (values : FixedArrayTable n ℚ) (hv : ∀ j, values.read j = i.length j)
    (items : List (Fin n)) (hi : items = i.uniformItems) : RationalTerminalPacking i × ℕ :=
  let result := GeneralPaperEqualPackingExecution.run model A values i.B items
  let hRows : result.1 = rationalPackedGroups i.length i.B i.uniformItems := by
    rw [GeneralPaperEqualPackingExecution.data, hi, funext hv]
  (ofRows i result.1 hRows, result.2)

theorem data {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel) (A : ℕ)
    (values : FixedArrayTable n ℚ) (hv : ∀ j, values.read j = i.length j)
    (items : List (Fin n)) (hi : items = i.uniformItems) :
    (run i model A values hv items hi).1 = RationalTerminalPacking.prepare i := by
  unfold run
  dsimp only
  apply ofRows_eq

theorem work {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel) (A : ℕ)
    (values : FixedArrayTable n ℚ) (hv : ∀ j, values.read j = i.length j)
    (items : List (Fin n)) (hi : items = i.uniformItems) (D W : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hBW : rationalWordWidth i.B ≤ W) (hW : 3 + 2 * binaryWordWidth D ≤ W)
    (hL : ∀ j, OnRationalLattice D (i.length j)) :
    (run i model A values hv items hi).2 ≤
      (12 * n + 12) * model.rat W + (12 * n + 24) * A + GeneralPaperEqualPackingExecution.unit A n * (2 * n + 4) := by
  have hItems : ∀ j ∈ items, OnRationalLattice D (values.read j) ∧ 0 ≤ values.read j ∧ values.read j ≤ i.B := by
    intro j _
    rw [hv j]
    exact ⟨hL j, (i.length_pos j).le, i.length_le j⟩
  have hCount : (rationalPackedGroups values.read i.B items).length ≤ 3 := by
    rw [funext hv, hi]
    have h := congrArg List.length (rationalPackedGroups_groups i.length i.B i.uniformItems)
    have he : (rationalPackedGroups i.length i.B i.uniformItems).length = i.groups.length := by
      simpa only [List.length_map, RationalTerminalLotto.groups] using h
    rw [he]
    rcases i.groups_count with h | h <;> omega
  have hLength : items.length ≤ n := by
    rw [hi]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  exact GeneralPaperEqualPackingExecution.bound model A values i.B D W hD hB hBW hW items hItems hCount hLength

end Blotto.GeneralPaperEqualMaterializedPacking
