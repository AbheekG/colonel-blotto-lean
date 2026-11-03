import Blotto.RationalFourCompleteProcessing
import Blotto.RationalOutputMapWork
import Blotto.RationalPreparationComparison

/-! The unsorted wrapper retains repeated sorting-network construction for
three selected fields in each machine/start input, plus the output permutation.
Dense four-row output keeps four producer allowances and one Boolean reader.
Metadata/backend/ownership and global compiler composition remain separate. -/

namespace Blotto.RationalFourSpec
open scoped BigOperators

def sortingNetworkBitCost (model : RationalCostModel) (L : Fin 3 → ℚ) : ℕ :=
  let p := rationalComparePermutation L 0 1
  let M := fun j => L (p j)
  let q := rationalComparePermutation M 1 2
  let N := fun j => M (q j)
  RationalPreparationComparison.bitCost model (L 0) (L 1) +
    RationalPreparationComparison.bitCost model (M 1) (M 2) +
      RationalPreparationComparison.bitCost model (N 0) (N 1)

theorem sortingNetworkBitCost_bound (model : RationalCostModel) (L : Fin 3 → ℚ) (s : ℕ)
    (hL : ∀ j, RationalHeight (L j) s) : sortingNetworkBitCost model L ≤ 9 * model.rat (1 + 2 * s) := by
  let p := rationalComparePermutation L 0 1
  let M := fun j => L (p j)
  let q := rationalComparePermutation M 1 2
  let N := fun j => M (q j)
  have h0 := RationalPreparationComparison.bitCost_bound model (L 0) (L 1) s (hL 0) (hL 1)
  have h1 := RationalPreparationComparison.bitCost_bound model (M 1) (M 2) s (hL _) (hL _)
  have h2 := RationalPreparationComparison.bitCost_bound model (N 0) (N 1) s (hL _) (hL _)
  change RationalPreparationComparison.bitCost model (L 0) (L 1) +
    RationalPreparationComparison.bitCost model (M 1) (M 2) + RationalPreparationComparison.bitCost model (N 0) (N 1) ≤ _
  omega

def inputFields (i : RationalFourSpec) : Fin 6 → ℚ :=
  ![i.input.B, i.input.u, i.input.v, i.input.w, i.input.ell, i.input.p]

def wrapperPreparationBitCost (model : RationalCostModel) (i : RationalFourSpec) : ℕ :=
  7 * sortingNetworkBitCost model i.length + 4 * ∑ j : Fin 6, rationalWordWidth (i.inputFields j)

theorem FieldsHeight.wrapperPreparationBitCost_bound {i : RationalFourSpec} {s : ℕ}
    (h : i.FieldsHeight s) (model : RationalCostModel) : i.wrapperPreparationBitCost model ≤ 87 * model.rat (1 + 2 * s) := by
  have hSort := sortingNetworkBitCost_bound model i.length s h.2.1
  have hInput := h.input
  have hFields : ∀ j, RationalHeight (i.inputFields j) s := by
    intro j
    fin_cases j
    · exact hInput.1
    · exact hInput.2.1
    · exact hInput.2.2.1
    · exact hInput.2.2.2.1
    · exact hInput.2.2.2.2.1
    · exact hInput.2.2.2.2.2
  have hCopies : (∑ j : Fin 6, rationalWordWidth (i.inputFields j)) ≤ 6 * model.rat (1 + 2 * s) := by
    calc
      _ ≤ ∑ _j : Fin 6, model.rat (1 + 2 * s) := Finset.sum_le_sum (fun j _ =>
        (rationalWordWidth_of_height (hFields j)).trans (model.word_le _))
      _ = _ := by simp
  unfold wrapperPreparationBitCost
  omega

noncomputable def completeProcessingAllowance (i : RationalFourSpec) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.wrapperPreparationBitCost model + i.input.entryPreparationAllowance model +
    4 * i.input.fourCompleteDataBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos +
      i.input.fourBooleanControlWork K outerBits scalarBits N bits pos hpos +
        i.permutationBitWork model K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.completeProcessingAllowance_bound {i : RationalFourSpec} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.completeProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        69175167 * model.rat (RationalFourInput.completeDataWidth (max s (K + 2))) +
          320 * RationalFourInput.fourControlWordHeight (max s (K + 2)) +
            (24 * RationalFourInput.fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) := by
  let w := max s (K + 2)
  let price := model.rat (RationalFourInput.completeDataWidth w)
  have hW : i.FieldsHeight w := ⟨h.1.mono (le_max_left s (K + 2)),
    fun j => (h.2.1 j).mono (le_max_left s (K + 2)),
    h.2.2.1.mono (le_max_left s (K + 2)), h.2.2.2.mono (le_max_left s (K + 2))⟩
  have hw := hs.trans (le_max_left s (K + 2))
  have hInput := hW.input
  have hWrapper := (hW.wrapperPreparationBitCost_bound model).trans (Nat.mul_le_mul_left 87 (model.monotone
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input w 73)) 1)))
  have hEntry := (hInput.entryPreparationAllowance_bound hw model).trans (Nat.mul_le_mul_left 375000
    (model.heightPrice_mono (le_refl w) (by decide : 39 ≤ 73)))
  have hData := h.input.fourCompleteDataBitWork_bound hs model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos
  have hControl := hInput.fourBooleanControlWork_bound hw K (le_max_right s (K + 2)) outerBits scalarBits N bits pos hpos
  have hMap := (h.permutationBitWork_bound hs model K outerBits scalarBits N bits pos hpos).trans (Nat.mul_le_mul_left 80
    (model.heightPrice_mono (le_refl w) (by decide : 72 ≤ 73)))
  change i.wrapperPreparationBitCost model ≤ 87 * price at hWrapper
  change i.input.entryPreparationAllowance model ≤ 375000 * price at hEntry
  change i.input.fourCompleteDataBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
    2268 * RationalNestedInput.preparationNumericBitWork c K + 17200000 * price at hData
  change i.permutationBitWork model K outerBits scalarBits N bits pos hpos ≤ 80 * price at hMap
  change i.completeProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
    9072 * RationalNestedInput.preparationNumericBitWork c K + 69175167 * price +
      320 * RationalFourInput.fourControlWordHeight w +
        (24 * RationalFourInput.fourControlWordHeight w + 28) * (162 + 2 * (N - pos))
  unfold completeProcessingAllowance
  omega

end Blotto.RationalFourSpec

namespace Blotto.RationalMixedGroupSpec

theorem FieldsHeight.fourCompleteProcessingAllowance_bound {i : RationalMixedGroupSpec 3} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.fourInput.completeProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        69175167 * model.rat (RationalFourInput.completeDataWidth (max s (K + 2))) +
          320 * RationalFourInput.fourControlWordHeight (max s (K + 2)) +
            (24 * RationalFourInput.fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) :=
  h.fourInput.completeProcessingAllowance_bound hs model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos

end Blotto.RationalMixedGroupSpec
