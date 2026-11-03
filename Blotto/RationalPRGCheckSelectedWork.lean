import Blotto.RationalPRGCheckCost

/-! A selected-stage work observer follows the primary Boolean checker and
the native list-all short circuit. Its primitive/read/write work is bounded
by the full-stage allowance, including every rejection gate. Metadata and
the physical backend remain separate. -/

namespace Blotto.RationalPRGCheckCode
open scoped BigOperators

def allBitWork (predicate : ℚ → Bool) (price : ℚ → ℕ) : List ℚ → ℕ
  | [] => 0
  | q :: rest => price q + if predicate q then allBitWork predicate price rest else 0

theorem allBitWork_bound (predicate : ℚ → Bool) (price : ℚ → ℕ) (row : List ℚ) :
    allBitWork predicate price row ≤ (row.map price).sum := by
  induction row with
  | nil => rfl
  | cons q rest ih =>
    simp only [allBitWork, List.map_cons, List.sum_cons]
    split <;> omega

def selectedBitWork {n : ℕ} (model : RationalCostModel) (values : Fin n → ℚ) (a b : ℚ) : ℕ :=
  let row := List.ofFn values
  2 * (∑ j, rationalWordWidth (values j)) +
    allBitWork (fun q => decide (0 < q)) (comparisonBitCost model 0) row + 6 +
      if row.all (fun q => decide (0 < q)) then
        rationalListSumBitCost model row + comparisonBitCost model row.sum 1 +
          if row.sum = 1 then comparisonBitCost model 0 a +
            if 0 < a then comparisonBitCost model 0 b +
              if 0 < b then comparisonBitCost model b a +
                if b ≤ a then allBitWork (fun q => decide (2 * a * q ≤ b)) (fieldBitCost model a b) row
                else 0
              else 0
            else 0
          else 0
      else 0

theorem selectedBitWork_le_allowance {n : ℕ} (model : RationalCostModel) (values : Fin n → ℚ) (a b : ℚ) :
    selectedBitWork model values a b ≤ bitAllowance model values a b := by
  have hPositive := allBitWork_bound (fun q => decide (0 < q)) (comparisonBitCost model 0) (List.ofFn values)
  have hField := allBitWork_bound (fun q => decide (2 * a * q ≤ b)) (fieldBitCost model a b) (List.ofFn values)
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn] at hPositive hField
  unfold selectedBitWork bitAllowance
  dsimp only
  split_ifs <;> omega

theorem selectedBitWork_original_bound {n : ℕ} (model : RationalCostModel) (values : Fin n → ℚ) (a b : ℚ) :
    selectedBitWork model values a b ≤
      (19 * n + 23) * model.rat (recognitionWidth n (3 + inputWordWidth values a b)) :=
  (selectedBitWork_le_allowance model values a b).trans (bitAllowance_original_bound model values a b)

theorem check_result_eq_bool {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) :
    (checkRationalPRG values a b).isSome = rationalPRGChecksBool values a b := by
  have h := (checkRationalPRG_isSome values a b).trans (rationalPRGChecksBool_iff values a b).symm
  cases hResult : (checkRationalPRG values a b).isSome <;>
    cases hBool : rationalPRGChecksBool values a b <;> simp_all

end Blotto.RationalPRGCheckCode
