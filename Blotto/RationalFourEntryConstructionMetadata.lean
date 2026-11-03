import Blotto.RationalFourSmallConstructionMetadata
import Blotto.RationalFourGluingConstructionMetadata
import Blotto.RationalFourEntryParameterMetadata

/-! Parent entry metadata retains two selected descriptor constructions and
the existing four parameter-table/two regime-test ledger. Start weight lists
retain full-prefix copy and index metadata. Backend and ownership stay separate. -/

namespace Blotto.RationalFourInput

def entryConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalFourInput) : ℕ :=
  entryParameterMetadataWork primitive c i + if hcase : (1 - i.p) * i.ell ≤ i.w then
    2 * gluingConstructionMetadataWork primitive c i hcase +
      rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn (i.gluingDescriptor hcase).weight)
  else
    2 * smallParentConstructionMetadataWork primitive c i (lt_of_not_ge hcase) +
      rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn (i.smallUniformLottery (lt_of_not_ge hcase)).weight) +
        indexedLoopMetadataBitWork primitive 0 3

def entryConstructionMetadataBound (c s : ℕ) : ℕ :=
  entryParameterMetadataBound c s + 2 * gluingConstructionMetadataBound c s +
    2 * smallParentConstructionMetadataBound c s +
      rationalEnvironmentMetadataBound c 81 (1 + 2 * expressionHeightBudget s 36) +
        rationalEnvironmentMetadataBound c 9 (1 + 2 * expressionHeightBudget s 35) + indexedLoopMetadataBound c 3

theorem FieldsHeight.entryConstructionMetadataWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    entryConstructionMetadataWork primitive c i ≤ entryConstructionMetadataBound c s := by
  have hParameters := h.entryParameterMetadataWork_bound hs primitive c hPrimitive
  unfold entryConstructionMetadataWork
  split
  · rename_i hcase
    have hParent := h.gluingConstructionMetadataWork_bound hs hcase primitive c hPrimitive
    have hStart := rationalEnvironmentMetadataWork_bound primitive c hPrimitive
      (FixedArrayTable.ofFn (i.gluingDescriptor hcase).weight) (1 + 2 * expressionHeightBudget s 36)
      (fun j => by
        rw [FixedArrayTable.read_ofFn]
        exact rationalWordWidth_of_height ((h.gluingDescriptor hs hcase).1 j))
    unfold entryConstructionMetadataBound
    omega
  · rename_i hcase
    have hParent := h.smallParentConstructionMetadataWork_bound hs (lt_of_not_ge hcase) primitive c hPrimitive
    have hStart := rationalEnvironmentMetadataWork_bound primitive c hPrimitive
      (FixedArrayTable.ofFn (i.smallUniformLottery (lt_of_not_ge hcase)).weight) (1 + 2 * expressionHeightBudget s 35)
      (fun j => by
        rw [FixedArrayTable.read_ofFn]
        exact rationalWordWidth_of_height ((h.smallUniformLottery hs (lt_of_not_ge hcase)).1 j))
    have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive 3
    unfold entryConstructionMetadataBound
    omega

noncomputable def entryPreparationWithConstructionMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (i : RationalFourInput) : ℕ := i.entryPreparationAllowance model + entryConstructionMetadataWork primitive c i

theorem FieldsHeight.entryPreparationWithConstructionMetadataWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) :
    entryPreparationWithConstructionMetadataWork model primitive c i ≤
      375000 * model.rat (1 + 2 * expressionHeightBudget s 39) + entryConstructionMetadataBound c s :=
  Nat.add_le_add (h.entryPreparationAllowance_bound hs model) (h.entryConstructionMetadataWork_bound hs primitive c hPrimitive)

end Blotto.RationalFourInput
