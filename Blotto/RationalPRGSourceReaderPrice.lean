import Blotto.RationalPRGReaderPrice
import Blotto.RationalPRGClassificationPrice

/-! Derivation costs for capacity reads at source pair preparation and the
selected retained tests. Original-value address/lookup, branch/control and
physical implementation costs are separate. -/

namespace Blotto.RationalPRGInput
open scoped BigOperators

def pairCapacityReaderBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (state : RationalActiveResources i.lengths) : ℕ :=
  match state.active with
  | a :: b :: _ => i.capacityReaderBitCost model a + i.capacityReaderBitCost model b
  | _ => 0

theorem pairCapacityReaderBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (state : RationalActiveResources i.lengths) :
    i.pairCapacityReaderBitCost model state ≤ 8 * model.rat (5 + 2 * i.inputWordWidth) := by
  unfold pairCapacityReaderBitCost
  split
  · rename_i a b tail h
    have ha := i.capacityReaderBitCost_bound model a
    have hb := i.capacityReaderBitCost_bound model b
    omega
  · exact Nat.zero_le _

theorem pairCapacityReaderBitCost_terminal {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (state : RationalActiveResources i.lengths) (hTerminal : state.active.length ≤ 1) :
    i.pairCapacityReaderBitCost model state = 0 := by
  unfold pairCapacityReaderBitCost
  split
  · rename_i a b tail h
    rw [h] at hTerminal
    simp only [List.length_cons] at hTerminal
    omega
  · rfl

def retainedCapacityReaderBitCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) : RationalResourceCursor i.lengths → ℕ
  | .ready _ => 0
  | .selected state a b tail he z =>
    let resource := (state.update a b tail he z).resource
    (if 0 < resource.allocation a then i.capacityReaderBitCost model a else 0) +
      (if 0 < resource.allocation b then i.capacityReaderBitCost model b else 0)

theorem retainedCapacityReaderBitCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (cursor : RationalResourceCursor i.lengths) :
    i.retainedCapacityReaderBitCost model cursor ≤ 8 * model.rat (5 + 2 * i.inputWordWidth) := by
  cases cursor with
  | ready state => exact Nat.zero_le _
  | selected state a b tail he z =>
    have ha := i.capacityReaderBitCost_bound model a
    have hb := i.capacityReaderBitCost_bound model b
    unfold retainedCapacityReaderBitCost
    dsimp only
    split_ifs <;> omega

def sourceReaderCharge {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (cursor : RationalResourceCursor i.lengths) : ℕ :=
  i.pairCapacityReaderBitCost model cursor.materialize + i.retainedCapacityReaderBitCost model cursor

theorem sourceReaderCharge_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (cursor : RationalResourceCursor i.lengths) :
    i.sourceReaderCharge model cursor ≤ 16 * model.rat (5 + 2 * i.inputWordWidth) := by
  have hp := i.pairCapacityReaderBitCost_bound model cursor.materialize
  have hr := i.retainedCapacityReaderBitCost_bound model cursor
  unfold sourceReaderCharge
  omega

def richInitialReaderTotal {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) : ℕ :=
  ∑ j, (i.richInitialReaderBitCost model j + i.capacityReaderBitCost model j)

def poorInitialReaderTotal {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) : ℕ :=
  ∑ j, (i.poorInitialReaderBitCost model j + i.capacityReaderBitCost model j)

theorem richInitialReaderTotal_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) :
    i.richInitialReaderTotal model ≤ 8 * n * model.rat (5 + 2 * i.inputWordWidth) := by
  have hSum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => i.richInitialReaderBitCost model j + i.capacityReaderBitCost model j)
    (g := fun _ => 8 * model.rat (5 + 2 * i.inputWordWidth)) (fun j _ => by
      have hr := i.richInitialReaderBitCost_bound model j
      have hc := i.capacityReaderBitCost_bound model j
      omega)
  have hConst : (∑ _j : Fin n, 8 * model.rat (5 + 2 * i.inputWordWidth)) = 8 * n * model.rat (5 + 2 * i.inputWordWidth) := by simp; ring
  exact hSum.trans_eq hConst

theorem poorInitialReaderTotal_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel) :
    i.poorInitialReaderTotal model ≤ 12 * n * model.rat (5 + 2 * i.inputWordWidth) := by
  have hSum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => i.poorInitialReaderBitCost model j + i.capacityReaderBitCost model j)
    (g := fun _ => 12 * model.rat (5 + 2 * i.inputWordWidth)) (fun j _ => by
      have hr := i.poorInitialReaderBitCost_bound model j
      have hc := i.capacityReaderBitCost_bound model j
      omega)
  have hConst : (∑ _j : Fin n, 12 * model.rat (5 + 2 * i.inputWordWidth)) = 12 * n * model.rat (5 + 2 * i.inputWordWidth) := by simp; ring
  exact hSum.trans_eq hConst

end Blotto.RationalPRGInput
