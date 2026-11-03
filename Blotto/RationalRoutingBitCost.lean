import Blotto.RationalRawGroupRouting
import Blotto.RationalPackingBitCost
import Blotto.PreparedGroupHeight

/-! Prices for retained raw-group routing and its zero-filled array patch.
One division constructs each routed coefficient. Its reduced numerator and
denominator remain bounded by the common denominator, even for small totals.
These prices cover rational primitives, copies and logical RAM cell traffic;
physical array-copy/ownership contracts remain separate. -/

namespace Blotto.RationalTerminalPacking

def entryCost {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (addressWidth : ℕ) (e : Fin n × GroupRoute i.groups.length) : ℕ :=
  match e.2.1 with
  | none => 0
  | some g =>
    rationalWordWidth (i.length e.1) + rationalWordWidth (p.groups.read g).2 +
      model.rat (RationalExpression.pairWidth (i.length e.1) (p.groups.read g).2) +
      rationalWordWidth e.2.2 + 4 * addressWidth

def routingBitCost {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (addressWidth : ℕ) : ℕ :=
  (p.routeAssignments.map (p.entryCost model addressWidth)).sum

theorem entryCost_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (addressWidth D W : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hW : 3 + 2 * binaryWordWidth D ≤ W)
    (e : Fin n × GroupRoute i.groups.length) (he : e ∈ p.routeAssignments) :
    p.entryCost model addressWidth e ≤ 4 * model.rat W + 4 * addressWidth := by
  rcases (p.mem_routeAssignments e).mp he with ⟨g, _, hEq⟩
  have hOption : e.2.1 = some g := congrArg Prod.fst hEq
  have hCoefficient : e.2.2 = i.length e.1 / i.partition.total g := congrArg Prod.snd hEq
  have hLength := (RationalPackingCost.unit_width hD (hL e.1)
    ⟨le_of_lt (i.length_pos e.1), (i.length_le e.1).trans hB⟩).trans hW
  have hTotal := (RationalPackingCost.unit_width hD (i.partition.total_on_lattice D hL g)
    ⟨le_of_lt (i.partition.total_pos g), (i.partition_total_le g).trans hB⟩).trans hW
  have hRatio := rationalWordWidth_of_height (i.partition.ratio_height_lattice D hD hL
    (fun j => (i.length_le j).trans hB) (fun g => (i.partition_total_le g).trans hB) e.1 g)
  change rationalWordWidth (i.length e.1 / i.partition.total g) ≤ 1 + 2 * binaryWordWidth D at hRatio
  have hRatioW : rationalWordWidth (i.length e.1 / i.partition.total g) ≤ W := by omega
  have hDiv := model.monotone
    (show RationalExpression.pairWidth (i.length e.1) (i.partition.total g) ≤ W from max_le hLength hTotal)
  have hLengthPrice := hLength.trans (model.word_le W)
  have hTotalPrice := hTotal.trans (model.word_le W)
  have hRatioPrice := hRatioW.trans (model.word_le W)
  simp only [entryCost, hOption, p.total_correct, hCoefficient]
  omega

theorem routingBitCost_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (addressWidth D W : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hW : 3 + 2 * binaryWordWidth D ≤ W) :
    p.routingBitCost model addressWidth ≤ n * (4 * model.rat W + 4 * addressWidth) := by
  have hPrice : (p.routeAssignments.map (p.entryCost model addressWidth)).sum ≤
      (p.routeAssignments.map (fun _ => 4 * model.rat W + 4 * addressWidth)).sum :=
    List.sum_le_sum (fun e he => p.entryCost_bound model addressWidth D W hD hB hL hW e he)
  have hSum : (p.routeAssignments.map (fun _ => 4 * model.rat W + 4 * addressWidth)).sum =
      p.routeAssignments.length * (4 * model.rat W + 4 * addressWidth) := by simp
  exact hPrice.trans (hSum ▸ Nat.mul_le_mul_right _ p.routeAssignments_length_le)

def tableSetupBitCost {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (addressWidth : ℕ) : ℕ :=
  n * (2 * addressWidth + rationalWordWidth (0 : ℚ)) +
    p.routingBitCost model addressWidth + 2 * i.groups.length * addressWidth

theorem tableSetupBitCost_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (addressWidth D W : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hW : 3 + 2 * binaryWordWidth D ≤ W)
    (hAddress : addressWidth ≤ W) :
    p.tableSetupBitCost model addressWidth ≤ (11 * n + 6) * model.rat W := by
  have h := p.routingBitCost_bound model addressWidth D W hD hB hL hW
  have hZero := (RationalPackingCost.unit_width hD (OnRationalLattice.zero D)
    (by norm_num : (0 : ℚ) ≤ 0 ∧ (0 : ℚ) ≤ 1)).trans hW
  have hZeroPrice := hZero.trans (model.word_le W)
  have hAddressPrice := hAddress.trans (model.word_le W)
  have hGroups : i.groups.length ≤ 3 := by rcases i.groups_count with he | he <;> omega
  unfold tableSetupBitCost
  nlinarith

end Blotto.RationalTerminalPacking

namespace Blotto.RationalTerminalLotto

def packingAndRoutingBitCost {n : ℕ} (i : RationalTerminalLotto n)
    (model : RationalCostModel) (addressWidth : ℕ) : ℕ :=
  RationalPackingCost.packed model addressWidth i.length i.B i.uniformItems +
    (RationalTerminalPacking.prepare i).tableSetupBitCost model addressWidth

theorem packingAndRoutingBitCost_bound {n : ℕ} (i : RationalTerminalLotto n)
    (model : RationalCostModel) (addressWidth D W : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) (hBW : rationalWordWidth i.B ≤ W)
    (hW : 3 + 2 * binaryWordWidth D ≤ W) (hAddress : addressWidth ≤ W) :
    i.packingAndRoutingBitCost model addressWidth ≤ (17 * n + 15) * model.rat W := by
  have hPack := i.packing_bitCost model addressWidth D W hD hB hL hBW hW hAddress
  have hRoute := (RationalTerminalPacking.prepare i).tableSetupBitCost_bound
    model addressWidth D W hD hB hL hW hAddress
  unfold packingAndRoutingBitCost
  nlinarith

def cacheWidth {n : ℕ} (i : RationalTerminalLotto n) (D : ℕ) : ℕ :=
  max (binaryWordWidth (n + 4)) (max (rationalWordWidth i.B) (3 + 2 * binaryWordWidth D))

theorem cacheWidth_le {n : ℕ} (i : RationalTerminalLotto n) (D : ℕ) :
    i.cacheWidth D ≤ binaryWordWidth (n + 4) + rationalWordWidth i.B + 3 + 2 * binaryWordWidth D := by
  unfold cacheWidth
  omega

theorem packingAndRoutingBitCost_input_width {n : ℕ} (i : RationalTerminalLotto n)
    (model : RationalCostModel) (D : ℕ) (hD : 0 < D) (hB : i.B ≤ 1)
    (hL : ∀ j, OnRationalLattice D (i.length j)) :
    i.packingAndRoutingBitCost model (binaryWordWidth (n + 4)) ≤
      (17 * n + 15) * model.rat (i.cacheWidth D) := by
  apply i.packingAndRoutingBitCost_bound model (binaryWordWidth (n + 4)) D (i.cacheWidth D) hD hB hL
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact le_max_left _ _

end Blotto.RationalTerminalLotto
