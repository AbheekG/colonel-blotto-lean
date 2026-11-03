import Blotto.RationalPRGCheckSelectedWork
import Blotto.RationalPRGNormalizationCost

/-! Aggregate input lengths pay every intermediate suffix sum in the actual
right-associated rational checker. No positivity, successful check or common
input-width promise is needed. These are arithmetic-model source prices;
parsing, table construction, metadata and backend calibration stay separate. -/
namespace Blotto.RationalAggregateRecognitionCost
open scoped BigOperators
set_option autoImplicit false

def totalWidth (row : List ℚ) : ℕ := (row.map rationalWordWidth).sum

theorem length_le_width (row : List ℚ) : row.length ≤ totalWidth row := by
  induction row with
  | nil => rfl
  | cons q rest ih =>
      have h : 1 ≤ rationalWordWidth q := by unfold rationalWordWidth; omega
      simp only [totalWidth,List.map_cons,List.sum_cons,List.length_cons] at *
      omega

theorem sum_height (row : List ℚ) : RationalHeight row.sum (totalWidth row+row.length+1) := by
  induction row with
  | nil => norm_num [totalWidth,RationalHeight]
  | cons q rest ih =>
      have h := (rationalHeight_of_wordWidth q).add ih
      simpa only [totalWidth,List.map_cons,List.sum_cons,List.length_cons,List.sum_cons,Nat.add_assoc] using h

theorem sum_width (row : List ℚ) : rationalWordWidth row.sum ≤ 4*totalWidth row+3 := by
  have h := rationalWordWidth_of_height (sum_height row)
  have hl := length_le_width row
  omega

theorem sum_work_bound (model : RationalCostModel) (row : List ℚ) (W : ℕ)
    (hW : 4*totalWidth row+3 ≤ W) : rationalListSumBitCost model row ≤ (4*row.length+1)*model.rat W := by
  induction row with
  | nil =>
      have hz : rationalWordWidth (0 : ℚ) = 3 := by decide
      simp only [totalWidth,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.zero_add] at hW
      simpa only [rationalListSumBitCost,hz,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.one_mul]
        using hW.trans (model.word_le W)
  | cons q rest ih =>
      have hTail : 4*totalWidth rest+3 ≤ W := by
        simp only [totalWidth,List.map_cons,List.sum_cons] at *
        omega
      have hHead : rationalWordWidth q ≤ W := by
        simp only [totalWidth,List.map_cons,List.sum_cons] at hW
        omega
      have hFull := (sum_width (q::rest)).trans hW
      have hRest := (sum_width rest).trans hTail
      have hCall := model.monotone (show RationalExpression.pairWidth q rest.sum ≤ W from max_le hHead hRest)
      have hh := hHead.trans (model.word_le W)
      have hr := hRest.trans (model.word_le W)
      have hf := hFull.trans (model.word_le W)
      have hi := ih hTail
      simp only [rationalListSumBitCost,List.length_cons,List.sum_cons] at *
      nlinarith

open RationalPRGCheckCode

theorem allowance_bound {n : ℕ} (model : RationalCostModel) (values : Fin n → ℚ) (a b : ℚ) :
    bitAllowance model values a b ≤ (19*n+23)*model.rat (32*(inputWordWidth values a b+3)) := by
  let L := inputWordWidth values a b
  let W := 32*(L+3)
  let P := model.rat W
  have hA : rationalWordWidth a ≤ L := by dsimp [L,inputWordWidth]; omega
  have hB : rationalWordWidth b ≤ L := by dsimp [L,inputWordWidth]; omega
  have hV (j : Fin n) : rationalWordWidth (values j) ≤ L := by
    have hh := Finset.single_le_sum (fun (j : Fin n) _ => Nat.zero_le (rationalWordWidth (values j)))
      (Finset.mem_univ j)
    dsimp [L,inputWordWidth]
    omega
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hLW : L ≤ W := by dsimp [W]; omega
  have hz : rationalWordWidth (0 : ℚ) ≤ W := by
    have hh : rationalWordWidth (0 : ℚ) = 3 := by decide
    dsimp [W]
    omega
  have ho : rationalWordWidth (1 : ℚ) ≤ W := by
    have hh : rationalWordWidth (1 : ℚ) = 3 := by decide
    dsimp [W]
    omega
  have hCopy : (∑ j, rationalWordWidth (values j)) ≤ n*P := by
    calc
      _ ≤ ∑ _j : Fin n, P := Finset.sum_le_sum (fun j _ => ((hV j).trans hLW).trans (model.word_le W))
      _ = _ := by simp
  have hPos : (∑ j, comparisonBitCost model 0 (values j)) ≤ 4*n*P := by
    have hh : (∑ j, comparisonBitCost model 0 (values j)) ≤ ∑ _j : Fin n, 4*P :=
      Finset.sum_le_sum (fun j _ => comparisonBitCost_bound model 0 (values j) W hW hz ((hV j).trans hLW))
    simpa [Nat.mul_assoc,Nat.mul_left_comm] using hh
  have hTotal : totalWidth (List.ofFn values) ≤ L := by
    dsimp [totalWidth,L,inputWordWidth]
    simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn]
    omega
  have hAggregate : 4*totalWidth (List.ofFn values)+3 ≤ W := by dsimp [W]; omega
  have hSum := sum_work_bound model (List.ofFn values) W hAggregate
  simp only [List.length_ofFn] at hSum
  have hSumCompare := comparisonBitCost_bound model (List.ofFn values).sum 1 W hW
    ((sum_width _).trans hAggregate) ho
  have hBudgetA := comparisonBitCost_bound model 0 a W hW hz (hA.trans hLW)
  have hBudgetB := comparisonBitCost_bound model 0 b W hW hz (hB.trans hLW)
  have hOrder := comparisonBitCost_bound model b a W hW (hB.trans hLW) (hA.trans hLW)
  have hFields : (∑ j, fieldBitCost model a b (values j)) ≤ 9*n*P := by
    have hWidth : 1+2*expressionHeightBudget (3+L) 2 ≤ W := by
      dsimp [W,expressionHeightBudget]
      norm_num only [Nat.reducePow]
      omega
    have ha := (rationalHeight_of_wordWidth a).mono (show rationalWordWidth a ≤ 3+L by omega)
    have hb := (rationalHeight_of_wordWidth b).mono (show rationalWordWidth b ≤ 3+L by omega)
    have hp := Nat.mul_le_mul_left 9 (model.monotone hWidth)
    have hh : (∑ j, fieldBitCost model a b (values j)) ≤ ∑ _j : Fin n, 9*P := by
      apply Finset.sum_le_sum
      intro j _
      exact (fieldBitCost_bound model a b (values j) (3+L) (by omega) ha hb
        ((rationalHeight_of_wordWidth (values j)).mono (by have hv := hV j; omega))).trans hp
    simpa [Nat.mul_assoc,Nat.mul_left_comm] using hh
  have hP : 1 ≤ P := hW.trans (model.word_le W)
  change bitAllowance model values a b ≤ (19*n+23)*P
  unfold bitAllowance
  dsimp only
  change rationalListSumBitCost model (List.ofFn values) ≤ (4*n+1)*P at hSum
  change comparisonBitCost model (List.ofFn values).sum 1 ≤ 4*P at hSumCompare
  change comparisonBitCost model 0 a ≤ 4*P at hBudgetA
  change comparisonBitCost model 0 b ≤ 4*P at hBudgetB
  change comparisonBitCost model b a ≤ 4*P at hOrder
  nlinarith only [hCopy,hPos,hSum,hSumCompare,hBudgetA,hBudgetB,hOrder,hFields,hP]

theorem selected_bound {n : ℕ} (model : RationalCostModel) (values : Fin n → ℚ) (a b : ℚ) :
    selectedBitWork model values a b ≤ (19*n+23)*model.rat (32*(inputWordWidth values a b+3)) :=
  (selectedBitWork_le_allowance model values a b).trans (allowance_bound model values a b)

theorem original_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) :
    selectedBitWork model i.values i.a i.b+i.normalizationBitWork model ≤
      (19*n+28)*model.rat (32*(i.originalInputWordWidth+3)) := by
  have hs := selected_bound model i.values i.a i.b
  have hn := i.normalizationBitWork_bound model
  have hp := Nat.mul_le_mul_left 5 (model.monotone
    (show 1+2*i.originalInputWordWidth ≤ 32*(i.originalInputWordWidth+3) by omega))
  change selectedBitWork model i.values i.a i.b ≤ (19*n+23)*model.rat (32*(i.originalInputWordWidth+3)) at hs
  nlinarith only [hs,hn,hp]

end Blotto.RationalAggregateRecognitionCost
