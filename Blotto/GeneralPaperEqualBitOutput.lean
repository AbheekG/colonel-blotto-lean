import Blotto.GeneralPaperEqualBitGroups

/-! One stored-route coordinate pass computes and prices each product once.
The group vector is already materialized, and runtime count comes from the
retained route array. Output words and array/control/reference work are paid. -/
namespace Blotto.GeneralPaperEqualBitOutput
open scoped BigOperators
open GeneralPaperEqualPreparedCache (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 900000

def coordinate {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (y : FixedArrayTable m ℚ) (j : Fin n) : ℚ × ℕ :=
  match (p.routes.table.read j).1 with
  | none => (0, rationalWordWidth (0 : ℚ) + 16 * A + 16)
  | some g => GeneralPaperRationalScalarStep.run model A .mul (p.routes.table.read j).2 (y.read g)

theorem coordinate_data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (y : FixedArrayTable m ℚ) (j : Fin n) :
    (coordinate p model A y j).1 = p.routes.routedValue y.read j := by
  unfold coordinate PreparedGroupOutput.routedValue
  cases (p.routes.table.read j).1 <;> rfl

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (y : FixedArrayTable m ℚ) : RationalResourceArray n × ℕ :=
  let returned := GeneralPaperSizedBitArray.run p.routes.table.data.size p.routes.table.size A (coordinate p model A y)
  (PaperStoredRowConstruction.resourceArray returned.1, returned.2 + 32 * A + 32)

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (y : FixedArrayTable m ℚ) :
    (run p model A y).1 = p.routes.emit y.read := by
  unfold run
  dsimp only
  rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data]
  simp only [coordinate_data]
  unfold PaperStoredRowConstruction.resourceArray PreparedGroupOutput.emit RationalProportionalGroups.emit
    RationalResourceArray.ofAllocation PreparedGroupOutput.routedValue
  simp only [FixedArrayTable.read_ofFn]
  rfl

theorem coordinate_work {n m k c t : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (y : FixedArrayTable m ℚ) (j : Fin n)
    (hc : 2 ≤ c) (hC : ∀ j, RationalHeight (p.routes.table.read j).2 c) (hY : ∀ g, RationalHeight (y.read g) t) :
    (coordinate p model A y j).2 ≤ 5 * model.rat (1 + 2 * expressionHeightBudget (max c t) 1) + 16 * A + 16 := by
  let H := max c t
  let S := expressionHeightBudget H 1
  have hm : H ≤ S := expressionHeightBudget_ge_input H 1
  unfold coordinate
  split
  · have h0 : rationalWordWidth (0 : ℚ) = 3 := by decide
    have hs : 3 ≤ 1 + 2 * S := by have hh := hc.trans ((le_max_left c t).trans hm); omega
    have hp := hs.trans (model.word_le _)
    dsimp only
    rw [h0]
    have hh : 3 ≤ 5 * model.rat (1 + 2 * expressionHeightBudget (max c t) 1) := by
      change 3 ≤ 5 * model.rat (1 + 2 * S)
      omega
    exact Nat.add_le_add_right (Nat.add_le_add_right hh (16 * A)) 16
  · rename_i g hg
    have h1 := (hC j).mono (le_max_left c t)
    have h2 := (hY g).mono (le_max_right c t)
    have ho := (h1.mul h2).mono (show H + H ≤ S by dsimp [S, expressionHeightBudget]; omega)
    exact GeneralPaperRationalScalarStep.work model A .mul _ _ S (h1.mono hm) (h2.mono hm) ho

theorem work {n m k c t : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (y : FixedArrayTable m ℚ)
    (hc : 2 ≤ c) (hC : ∀ j, RationalHeight (p.routes.table.read j).2 c) (hY : ∀ g, RationalHeight (y.read g) t) :
    (run p model A y).2 ≤ 5 * n * model.rat (1 + 2 * expressionHeightBudget (max c t) 1) +
      64 * (n + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead (fun w => w) A n n := by
  have hs : (∑ j, (coordinate p model A y j).2) ≤
      n * (5 * model.rat (1 + 2 * expressionHeightBudget (max c t) 1) + 16 * A + 16) := by
    calc
      _ ≤ ∑ _j : Fin n, (5 * model.rat (1 + 2 * expressionHeightBudget (max c t) 1) + 16 * A + 16) :=
        Finset.sum_le_sum (fun j _ => coordinate_work p model A y j hc hC hY)
      _ = _ := by simp
  unfold run
  dsimp only
  rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_work]
  nlinarith only [hs]

end Blotto.GeneralPaperEqualBitOutput
