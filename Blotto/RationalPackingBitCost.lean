import Blotto.RationalPackingLabels
import Blotto.SignedLatticeSize
import Blotto.RationalExpressionBitCost

/-! Operand-sized prices for the selected cached packing scan. A common
denominator bounds running and rejected tentative sums independently of item
count. Cell work uses a supplied address-word width; this is a RAM primitive
ledger, not a native allocator timing claim. -/

namespace Blotto
namespace RationalPackingCost

theorem unit_width {D : ℕ} (hD : 0 < D) {q : ℚ} (hq : OnRationalLattice D q)
    (hBox : 0 ≤ q ∧ q ≤ 1) : rationalWordWidth q ≤ 3 + 2 * binaryWordWidth D := by
  have h := rationalWordWidth_abs_lattice_bound (M := 1) hD hq (by
    rw [abs_of_nonneg hBox.1]; exact hBox.2)
  have hone : binaryWordWidth 1 = 1 := by decide
  rw [hone] at h
  omega

theorem tentative_width {D : ℕ} (hD : 0 < D) {s q : ℚ}
    (hs : OnRationalLattice D s) (hq : OnRationalLattice D q)
    (hsBox : 0 ≤ s ∧ s ≤ 1) (hqBox : 0 ≤ q ∧ q ≤ 1) :
    rationalWordWidth (s + q) ≤ 3 + 2 * binaryWordWidth D := by
  have hAbs : |s + q| ≤ (2 : ℚ) := by
    rw [abs_of_nonneg (add_nonneg hsBox.1 hqBox.1)]
    linarith [hsBox.2, hqBox.2]
  have h := rationalWordWidth_abs_lattice_bound (M := 2) hD (hs.add hq) hAbs
  have htwo : binaryWordWidth 2 = 2 := by decide
  simpa only [htwo] using h

def scan {α : Type*} (model : RationalCostModel) (addressWidth : ℕ) (L : α → ℚ) (B : ℚ) :
    List α → ℚ → List α → ℕ
  | current, s, [] => rationalWordWidth s + (current.length + 2) * addressWidth
  | current, s, x :: rest =>
    let itemLength := L x
    let next := s + itemLength
    let body := rationalWordWidth itemLength +
      model.rat (RationalExpression.pairWidth s itemLength) +
      model.rat (RationalExpression.pairWidth next B) + 2 * addressWidth
    if next ≤ B then body + scan model addressWidth L B (x :: current) next rest
    else body + rationalWordWidth s + (current.length + 2) * addressWidth +
      scan model addressWidth L B [x] itemLength rest

theorem scan_bound {α : Type*} (model : RationalCostModel) (addressWidth : ℕ)
    (L : α → ℚ) (B : ℚ) (D W : ℕ) (hD : 0 < D) (hB : B ≤ 1)
    (hBW : rationalWordWidth B ≤ W) (hW : 3 + 2 * binaryWordWidth D ≤ W)
    (current rest : List α) (s : ℚ) (hs : OnRationalLattice D s) (hsBox : 0 ≤ s ∧ s ≤ B)
    (hRest : ∀ x ∈ rest, OnRationalLattice D (L x) ∧ 0 ≤ L x ∧ L x ≤ B) :
    scan model addressWidth L B current s rest ≤
      (3 * rest.length + (rationalPackSumsAux L B current s rest).length) * model.rat W +
      (3 * rest.length + current.length + 2 * (rationalPackSumsAux L B current s rest).length) * addressWidth := by
  induction rest generalizing current s with
  | nil =>
    have hsW := (unit_width hD hs ⟨hsBox.1, hsBox.2.trans hB⟩).trans hW
    have hsPrice := hsW.trans (model.word_le W)
    simp only [scan, rationalPackSumsAux, List.length_singleton, List.length_nil]
    nlinarith
  | cons x rest ih =>
    have hx := hRest x (by simp)
    have hr := fun y hy => hRest y (List.mem_cons_of_mem x hy)
    have hsW := (unit_width hD hs ⟨hsBox.1, hsBox.2.trans hB⟩).trans hW
    have hxW := (unit_width hD hx.1 ⟨hx.2.1, hx.2.2.trans hB⟩).trans hW
    have hnW := (tentative_width hD hs hx.1 ⟨hsBox.1, hsBox.2.trans hB⟩
      ⟨hx.2.1, hx.2.2.trans hB⟩).trans hW
    have hCopy := hxW.trans (model.word_le W)
    have hSum := model.monotone (show RationalExpression.pairWidth s (L x) ≤ W from max_le hsW hxW)
    have hCmp := model.monotone (show RationalExpression.pairWidth (s + L x) B ≤ W from max_le hnW hBW)
    have hClose := hsW.trans (model.word_le W)
    rw [scan, rationalPackSumsAux]
    split_ifs with hFit
    · have hRec := ih (x :: current) (s + L x) (hs.add hx.1)
        ⟨add_nonneg hsBox.1 hx.2.1, hFit⟩ hr
      simp only [List.length_cons] at hRec ⊢
      nlinarith
    · have hRec := ih [x] (L x) hx.1 hx.2 hr
      simp only [List.length_cons, List.length_nil] at hRec ⊢
      nlinarith

def packed {α : Type*} (model : RationalCostModel) (addressWidth : ℕ) (L : α → ℚ) (B : ℚ) :
    List α → ℕ
  | [] => 0
  | x :: rest => rationalWordWidth (L x) + 2 * addressWidth +
      scan model addressWidth L B [x] (L x) rest

theorem packed_bound {α : Type*} (model : RationalCostModel) (addressWidth : ℕ)
    (L : α → ℚ) (B : ℚ) (D W : ℕ) (hD : 0 < D) (hB : B ≤ 1)
    (hBW : rationalWordWidth B ≤ W) (hW : 3 + 2 * binaryWordWidth D ≤ W)
    (items : List α) (hItems : ∀ x ∈ items, OnRationalLattice D (L x) ∧ 0 ≤ L x ∧ L x ≤ B) :
    packed model addressWidth L B items ≤
      (3 * items.length + (rationalPackedGroups L B items).length) * model.rat W +
      (3 * items.length + 2 * (rationalPackedGroups L B items).length) * addressWidth := by
  cases items with
  | nil => simp [packed, rationalPackedGroups]
  | cons x rest =>
    have hx := hItems x (by simp)
    have hRec := scan_bound model addressWidth L B D W hD hB hBW hW [x] rest (L x)
      hx.1 hx.2 (fun y hy => hItems y (List.mem_cons_of_mem x hy))
    have hCopy := ((unit_width hD hx.1 ⟨hx.2.1, hx.2.2.trans hB⟩).trans hW).trans (model.word_le W)
    simp only [packed, rationalPackedGroups, List.length_cons, List.length_nil] at hRec ⊢
    nlinarith

end RationalPackingCost
namespace RationalTerminalLotto

theorem packing_bitCost {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel)
    (addressWidth D W : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j))
    (hBW : rationalWordWidth i.B ≤ W) (hW : 3 + 2 * binaryWordWidth D ≤ W)
    (hAddress : addressWidth ≤ W) :
    RationalPackingCost.packed model addressWidth i.length i.B i.uniformItems ≤
      (6 * n + 9) * model.rat W := by
  have h := RationalPackingCost.packed_bound model addressWidth i.length i.B D W hD hB hBW hW
    i.uniformItems (fun j _ => ⟨hL j, le_of_lt (i.length_pos j), i.length_le j⟩)
  have hCount : (rationalPackedGroups i.length i.B i.uniformItems).length ≤ 3 := by
    have he := congrArg List.length (rationalPackedGroups_groups i.length i.B i.uniformItems)
    have hEq : (rationalPackedGroups i.length i.B i.uniformItems).length = i.groups.length := by
      simpa only [List.length_map, RationalTerminalLotto.groups] using he
    rw [hEq]
    rcases i.groups_count with he | he <;> omega
  have hItems : i.uniformItems.length ≤ n :=
    (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  have hPrice := hAddress.trans (model.word_le W)
  nlinarith

end RationalTerminalLotto
end Blotto
