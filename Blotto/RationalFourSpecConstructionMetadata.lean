import Blotto.RationalFourEntryConstructionMetadata
import Blotto.RationalFourConstructionMetadataWork

/-! The unsorted wrapper retains its repeated sorting-loop and copied-input
metadata. Parent preparation and runtime terminal factories add to the existing
data/control processing component. This does not certify a physical backend. -/

namespace Blotto.RationalFourSpec

def wrapperConstructionMetadataWork (primitive : ℕ → ℕ) (i : RationalFourSpec) : ℕ :=
  7 * indexedLoopMetadataBitWork primitive 0 3 +
    4 * rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn i.inputFields)

def wrapperConstructionMetadataBound (c s : ℕ) : ℕ :=
  7 * indexedLoopMetadataBound c 3 + 4 * rationalEnvironmentMetadataBound c 6 (1 + 2 * s)

theorem FieldsHeight.wrapperConstructionMetadataWork_bound {i : RationalFourSpec} {s : ℕ}
    (h : i.FieldsHeight s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    wrapperConstructionMetadataWork primitive i ≤ wrapperConstructionMetadataBound c s := by
  have hInput := h.input
  have hFields : ∀ j, RationalHeight ((FixedArrayTable.ofFn i.inputFields).read j) s := by
    intro j
    rw [FixedArrayTable.read_ofFn]
    fin_cases j
    · exact hInput.1
    · exact hInput.2.1
    · exact hInput.2.2.1
    · exact hInput.2.2.2.1
    · exact hInput.2.2.2.2.1
    · exact hInput.2.2.2.2.2
  have hCopy := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
    (fun j => rationalWordWidth_of_height (hFields j))
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive 3
  exact Nat.add_le_add (Nat.mul_le_mul_left 7 hLoop) (Nat.mul_le_mul_left 4 hCopy)

noncomputable def completeProcessingWithConstructionMetadataWork (i : RationalFourSpec)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.completeProcessingAllowance model primitive copyResources K outerBits scalarBits N bits pos hpos +
    wrapperConstructionMetadataWork primitive i +
      RationalFourInput.entryConstructionMetadataWork primitive c i.input +
        i.runtimeConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.completeProcessingWithConstructionMetadataWork_bound {i : RationalFourSpec} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.completeProcessingWithConstructionMetadataWork model primitive c copyResources K outerBits scalarBits N bits pos hpos ≤
      9072 * RationalNestedInput.preparationNumericBitWork c K +
        69175167 * model.rat (RationalFourInput.completeDataWidth (max s (K + 2))) +
          320 * RationalFourInput.fourControlWordHeight (max s (K + 2)) +
            (24 * RationalFourInput.fourControlWordHeight (max s (K + 2)) + 28) * (162 + 2 * (N - pos)) +
              wrapperConstructionMetadataBound c s + RationalFourInput.entryConstructionMetadataBound c s +
                2592 * RationalTerminalResources.profileConstructionMetadataBound c
                  (expressionHeightBudget (max s (K + 2)) 21) K :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (h.completeProcessingAllowance_bound hs model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos)
    (h.wrapperConstructionMetadataWork_bound primitive c hPrimitive))
    (h.input.entryConstructionMetadataWork_bound hs primitive c hPrimitive))
    (h.runtimeConstructionMetadataWork_bound hs primitive c hPrimitive K outerBits scalarBits N bits pos hpos)

end Blotto.RationalFourSpec
