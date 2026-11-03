import Blotto.RationalTerminalGroupCompleteProcessing

/-! Cached group totals supply the actual uniform/mixed packet fields.
Rational read/write copies and the mixed pivot ratio are priced. Pivot scans,
record/list/index representation, packing and backend/ownership are separate. -/

namespace Blotto.RationalTerminalLotto
open scoped BigOperators

def groupPacketWordBitCost {n : ℕ} (i : RationalTerminalLotto n) : ℕ :=
  match i.pivot with
  | none => 2 * (rationalWordWidth i.B + ∑ g : Fin i.groups.length, rationalWordWidth (i.partition.total g))
  | some pivot => 2 * (rationalWordWidth i.B + (∑ g : Fin i.groups.length, rationalWordWidth (i.partition.total g)) +
      rationalWordWidth (i.length pivot) + rationalWordWidth (i.resource pivot / i.length pivot))

def groupRatioBitCost {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel) : ℕ :=
  match i.pivot with
  | none => 0
  | some pivot => rationalWordWidth (i.resource pivot) + rationalWordWidth (i.length pivot) +
      model.rat (RationalExpression.pairWidth (i.resource pivot) (i.length pivot)) +
        rationalWordWidth (i.resource pivot / i.length pivot)

theorem OnLattice.groupPacketWordBitCost_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hBudget : RationalHeight i.B s)
    (hWidth : binaryWordWidth D ≤ s) (model : RationalCostModel) :
    i.groupPacketWordBitCost ≤ 12 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  let price := model.rat (1 + 2 * expressionHeightBudget s 1)
  have hm := expressionHeightBudget_ge_input s 1
  have hBw := (rationalWordWidth_of_height (hBudget.mono hm)).trans (model.word_le _)
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with hc | hc <;> omega
  have hTotals : (∑ g : Fin i.groups.length, rationalWordWidth (i.partition.total g)) ≤ i.groups.length * price := by
    calc
      _ ≤ ∑ _g : Fin i.groups.length, price := Finset.sum_le_sum (fun g _ =>
        (rationalWordWidth_of_height ((h.total_height hD hB g).mono (hWidth.trans hm))).trans (model.word_le _))
      _ = _ := by simp
  unfold groupPacketWordBitCost
  split
  · nlinarith
  · rename_i pivot hSome
    have hLength := (h.length_height hD hB pivot).mono hWidth
    have hResource := (h.resource_height hD hB pivot).mono hWidth
    have hL0 : RationalHeight (i.length pivot) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hLength
    have hR0 : RationalHeight (i.resource pivot) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hResource
    have hRatio : RationalHeight (i.resource pivot / i.length pivot) (expressionHeightBudget s 1) := hR0.div_level hL0
    have hLw := (rationalWordWidth_of_height (hLength.mono hm)).trans (model.word_le _)
    have hQw := (rationalWordWidth_of_height hRatio).trans (model.word_le _)
    nlinarith

theorem OnLattice.groupRatioBitCost_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ)
    (hWidth : binaryWordWidth D ≤ s) (model : RationalCostModel) :
    i.groupRatioBitCost model ≤ 4 * model.rat (1 + 2 * expressionHeightBudget s 1) := by
  unfold groupRatioBitCost
  split
  · exact Nat.zero_le _
  · rename_i pivot hSome
    have hm := expressionHeightBudget_ge_input s 1
    have hLength := (h.length_height hD hB pivot).mono hWidth
    have hResource := (h.resource_height hD hB pivot).mono hWidth
    have hL0 : RationalHeight (i.length pivot) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hLength
    have hR0 : RationalHeight (i.resource pivot) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hResource
    have hRatio : RationalHeight (i.resource pivot / i.length pivot) (expressionHeightBudget s 1) := hR0.div_level hL0
    have hLw := (rationalWordWidth_of_height (hLength.mono hm)).trans (model.word_le _)
    have hRw := (rationalWordWidth_of_height (hResource.mono hm)).trans (model.word_le _)
    have hQw := (rationalWordWidth_of_height hRatio).trans (model.word_le _)
    have hCall := model.monotone (RationalExpression.pairWidth_height (hResource.mono hm) (hLength.mono hm))
    omega

noncomputable def inputCouplingAndEmissionAllowance {n : ℕ} (i : RationalTerminalLotto n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.groupPacketWordBitCost + i.groupRatioBitCost model +
    i.couplingAndEmissionAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos

theorem OnLattice.inputCouplingAndEmissionAllowance_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.inputCouplingAndEmissionAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        (70000020 + 8 * n) * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 75) +
          320 * terminalCouplingWordHeight (max s (K + 2)) +
            (24 * terminalCouplingWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) := by
  have hCopy := (h.groupPacketWordBitCost_bound hD hB s hBudget hWidth model).trans (Nat.mul_le_mul_left 12
    (model.heightPrice_mono (le_max_left s (K + 2)) (by decide : 1 ≤ 75)))
  have hRatio := (h.groupRatioBitCost_bound hD hB s hWidth model).trans (Nat.mul_le_mul_left 4
    (model.heightPrice_mono (le_max_left s (K + 2)) (by decide : 1 ≤ 75)))
  have hCore := h.couplingAndEmissionAllowance_bound hD hB s hs hBudget hWidth model primitive c hPrimitive copyResources K
    outerBits scalarBits N bits pos hpos
  unfold inputCouplingAndEmissionAllowance
  nlinarith

end Blotto.RationalTerminalLotto
