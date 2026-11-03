import Blotto.RationalOutputMapWork
import Blotto.RationalExpressionInputOccurrences

/-! Dense reflection reads each uncached input coordinate four times. A
fourfold data/primitive allowance therefore retains producer work explicitly,
while the original Boolean-control observer runs once. This is a conservative
labelled allowance; later maps/fallback, metadata/backend/ownership are separate. -/

namespace Blotto.RationalFourInput

noncomputable def reflectedOutputProcessingAllowance (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let system := i.reflectedResourceSystem hcase
  4 * system.localDataOutputBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos +
    system.localBooleanControlWork K outerBits scalarBits N bits pos hpos +
      i.reflectedMapBitWork hcase model K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.reflectedOutputProcessingAllowance_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.reflectedOutputProcessingAllowance hcase model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      232 * RationalNestedInput.preparationNumericBitWork c K +
        1992064 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 73) +
          76 * ((expressionHeightBudget (max s (K + 2)) 68 + 1) * 19) +
            (24 * ((expressionHeightBudget (max s (K + 2)) 68 + 1) * 19) + 28) * (40 + 2 * (N - pos)) := by
  let w := max s (K + 2)
  let price := model.rat (1 + 2 * expressionHeightBudget w 73)
  have hw := hs.trans (le_max_left s (K + 2))
  have hSystem := (h.mono (le_max_left s (K + 2))).reflectedResourceSystem hw hcase
  have hPrecision := (le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 14)
  have hd := hSystem.localDataOutputBitWork_bound (hw.trans (expressionHeightBudget_ge_input w 14))
    model primitive c hPrimitive copyResources K hPrecision outerBits scalarBits N bits pos hpos
  have hc := hSystem.localBooleanControlWork_bound (hw.trans (expressionHeightBudget_ge_input w 14))
    K hPrecision outerBits scalarBits N bits pos hpos
  unfold RationalNestedResourceSystem.localDataOutputWidth at hd
  unfold RationalNestedResourceSystem.localControlWordHeight at hc
  simp only [expressionHeightBudget_comp] at hd hc
  have hm := (h.reflectedMapBitWork_bound hs hcase model K outerBits scalarBits N bits pos hpos).trans
    (Nat.mul_le_mul_left 64 (model.heightPrice_mono (le_refl w) (by decide : 72 ≤ 73)))
  change i.reflectedMapBitWork hcase model K outerBits scalarBits N bits pos hpos ≤ 64 * price at hm
  change (i.reflectedResourceSystem hcase).localDataOutputBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
    58 * RationalNestedInput.preparationNumericBitWork c K + 498000 * price at hd
  change (i.reflectedResourceSystem hcase).localBooleanControlWork K outerBits scalarBits N bits pos hpos ≤
    76 * ((expressionHeightBudget w 68 + 1) * 19) +
      (24 * ((expressionHeightBudget w 68 + 1) * 19) + 28) * (40 + 2 * (N - pos)) at hc
  change i.reflectedOutputProcessingAllowance hcase model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
    232 * RationalNestedInput.preparationNumericBitWork c K + 1992064 * price +
      76 * ((expressionHeightBudget w 68 + 1) * 19) +
        (24 * ((expressionHeightBudget w 68 + 1) * 19) + 28) * (40 + 2 * (N - pos))
  unfold reflectedOutputProcessingAllowance
  dsimp only
  omega

end Blotto.RationalFourInput
