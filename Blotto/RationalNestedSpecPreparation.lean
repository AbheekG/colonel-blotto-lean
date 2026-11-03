import Blotto.RationalOrderedProfilePreparation
import Blotto.RationalThreeSpecPreparation

/-! Endpoint mixture weights and either coordinate order retain one nested
profile construction envelope. Comparison/data/padding/permutation components
are explicit; caller invocation counts and physical storage remain separate. -/

namespace Blotto.RationalThreeSpecCode
open scoped BigOperators

def inputFieldCopyBitCost (i : RationalThreeSpec) : ℕ :=
  ∑ j : Fin 5, rationalWordWidth ((environment i).read j)

theorem inputFieldCopyBitCost_bound (model : RationalCostModel) (i : RationalThreeSpec) (s : ℕ)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    inputFieldCopyBitCost i ≤ 5 * model.rat (1 + 2 * s) := by
  calc
    _ ≤ ∑ _j : Fin 5, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
      (rationalWordWidth_of_height (hEnv j)).trans (model.word_le _))
    _ = _ := by simp

noncomputable def endpointPreparedBitCost (model : RationalCostModel) (i : RationalThreeSpec) : ℕ :=
  inputFieldCopyBitCost i + preparedSpecBitCost model i + i.segmentLottery.paddingBitCost 9 0

theorem endpointPreparedBitCost_bound (model : RationalCostModel) (i : RationalThreeSpec) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    endpointPreparedBitCost model i ≤ 3051 * model.rat (1 + 2 * expressionHeightBudget s 18) := by
  have hm := model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input s 18)) 1)
  have hInput := (inputFieldCopyBitCost_bound model i s hEnv).trans (Nat.mul_le_mul_left 5 hm)
  have hSpec := preparedSpecBitCost_bound model i s hs hEnv
  have hPad := i.segmentLottery.paddingBitCost_bound model 9 0 _
    (hs.trans (expressionHeightBudget_ge_input s 18)) (descriptor_height i s hs hEnv)
  change i.segmentLottery.paddingBitCost 9 0 ≤ 126 * model.rat (1 + 2 * expressionHeightBudget s 18) at hPad
  unfold endpointPreparedBitCost
  omega

end Blotto.RationalThreeSpecCode
namespace Blotto.RationalNestedSpec
open scoped BigOperators

def sortedInputFields (i : RationalNestedSpec) : Fin 6 → ℚ := ![i.M, min i.a i.d, max i.a i.d, i.c, i.t, i.q]

def sortingDataBitCost (model : RationalCostModel) (i : RationalNestedSpec) : ℕ :=
  3 * RationalPreparationComparison.bitCost model i.a i.d + ∑ j : Fin 6, rationalWordWidth (i.sortedInputFields j)

theorem FieldsHeight.sortingDataBitCost_bound {i : RationalNestedSpec} {s : ℕ}
    (h : i.FieldsHeight s) (model : RationalCostModel) :
    i.sortingDataBitCost model ≤ 15 * model.rat (1 + 2 * s) := by
  have hCmp := RationalPreparationComparison.bitCost_bound model i.a i.d s h.2.1 h.2.2.1
  have hFields : ∀ j, RationalHeight (i.sortedInputFields j) s := by
    intro j
    fin_cases j
    · exact h.1
    · exact h.2.1.min h.2.2.1
    · exact h.2.1.max h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2
  have hCopies : (∑ j : Fin 6, rationalWordWidth (i.sortedInputFields j)) ≤ 6 * model.rat (1 + 2 * s) := by
    calc
      _ ≤ ∑ _j : Fin 6, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (hFields j)).trans (model.word_le _))
      _ = _ := by simp
  unfold sortingDataBitCost
  omega

noncomputable def profilePreparedBitCost (model : RationalCostModel) (primitive : ℕ → ℕ)
    (i : RationalNestedSpec) (K : ℕ) (outerBits : Fin K → Bool) : ℕ :=
  RationalPreparationComparison.bitCost model i.q 0 + if hq0 : i.q = 0 then
    RationalThreeSpecCode.endpointPreparedBitCost model (i.longInput hq0)
  else RationalPreparationComparison.bitCost model i.q 1 + if hq1 : i.q = 1 then
    RationalThreeSpecCode.endpointPreparedBitCost model (i.shortInput hq1)
  else
    let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
    i.sortingDataBitCost model + j.profilePreparedBitCost model primitive K outerBits +
      if i.a ≤ i.d then 0 else (PreparedSegmentDescriptor.prepare (i.profile K outerBits)).payloadBitCost

theorem FieldsHeight.profilePreparedBitCost_common {i : RationalNestedSpec} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool) :
    i.profilePreparedBitCost model primitive K outerBits ≤
      RationalNestedInput.preparationNumericBitWork c K + 8000 * model.rat (RationalNestedInput.preparationWidth s) := by
  let price := model.rat (RationalNestedInput.preparationWidth s)
  have hm : model.rat (1 + 2 * s) ≤ price := model.monotone
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input s 45)) 1)
  have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hGuard0 := (RationalPreparationComparison.bitCost_bound model i.q 0 s h.2.2.2.2.2 hZero).trans (Nat.mul_le_mul_left 3 hm)
  have hGuard1 := (RationalPreparationComparison.bitCost_bound model i.q 1 s h.2.2.2.2.2 hOne).trans (Nat.mul_le_mul_left 3 hm)
  change i.profilePreparedBitCost model primitive K outerBits ≤ RationalNestedInput.preparationNumericBitWork c K + 8000 * price
  unfold profilePreparedBitCost
  split
  · rename_i hq0
    have hp := (RationalThreeSpecCode.endpointPreparedBitCost_bound model (i.longInput hq0) s hs (h.longInput hs hq0)).trans
      (Nat.mul_le_mul_left 3051 (model.heightPrice_mono (le_refl s) (by decide : 18 ≤ 45)))
    change RationalThreeSpecCode.endpointPreparedBitCost model (i.longInput hq0) ≤ 3051 * price at hp
    omega
  · split
    · rename_i hq0 hq1
      have hp := (RationalThreeSpecCode.endpointPreparedBitCost_bound model (i.shortInput hq1) s hs (h.shortInput hs hq1)).trans
        (Nat.mul_le_mul_left 3051 (model.heightPrice_mono (le_refl s) (by decide : 18 ≤ 45)))
      change RationalThreeSpecCode.endpointPreparedBitCost model (i.shortInput hq1) ≤ 3051 * price at hp
      omega
    · rename_i hq0 hq1
      have hSort := (h.sortingDataBitCost_bound model).trans (Nat.mul_le_mul_left 15 hm)
      have hCore := (h.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)).profilePreparedBitCost_common
        hs model primitive c hPrimitive K hK outerBits
      change (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)).profilePreparedBitCost model primitive K outerBits ≤
        RationalNestedInput.preparationNumericBitWork c K + 7800 * price at hCore
      have hTable := h.profile hs K outerBits
      rw [max_eq_left hK] at hTable
      have hPayload := (PreparedSegmentDescriptor.prepare (i.profile K outerBits)).payloadBitCost_bound _ hTable
      have hCopies := hPayload.trans (Nat.mul_le_mul_left 126 (model.word_le (RationalNestedInput.preparationWidth s)))
      change (PreparedSegmentDescriptor.prepare (i.profile K outerBits)).payloadBitCost ≤ 126 * price at hCopies
      dsimp only
      split <;> omega

theorem FieldsHeight.profilePreparedBitCost_bound {i : RationalNestedSpec} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits : Fin K → Bool) :
    i.profilePreparedBitCost model primitive K outerBits ≤
      RationalNestedInput.preparationNumericBitWork c K +
        8000 * model.rat (RationalNestedInput.preparationWidth (max s (K + 2))) :=
  (h.mono (le_max_left _ _)).profilePreparedBitCost_common (hs.trans (le_max_left _ _))
    model primitive c hPrimitive K (le_max_right _ _) outerBits

end Blotto.RationalNestedSpec
