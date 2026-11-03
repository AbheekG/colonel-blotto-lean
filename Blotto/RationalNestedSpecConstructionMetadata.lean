import Blotto.RationalPermutationMetadata

/-! Endpoint/spec wrapping retains the full endpoint construction or sorted
interior profile and selected swapped table. Written fields and actual branch
prices are preserved; caller/physical contracts remain separate. -/

namespace Blotto.RationalNestedSpec

def sortingFieldsMetadataWork (primitive : ℕ → ℕ) (i : RationalNestedSpec) : ℕ :=
  rationalArrayCopyWork (List.ofFn i.sortedInputFields) 0 + indexedLoopMetadataBitWork primitive 0 6

def sortingFieldsMetadataBound (c s : ℕ) : ℕ := 72 * (1 + 2 * s) + indexedLoopMetadataBound c 6

theorem FieldsHeight.sortingFieldsMetadataWork_bound {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    sortingFieldsMetadataWork primitive i ≤ sortingFieldsMetadataBound c s := by
  have hFields : ∀ j, RationalHeight (i.sortedInputFields j) s := by
    intro j
    fin_cases j
    · exact h.1
    · exact h.2.1.min h.2.2.1
    · exact h.2.1.max h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2
  have hCopy := rationalArrayCopyWork_bound (List.ofFn i.sortedInputFields) 0
  have hWords := rationalWordWidth_sum_bound (List.ofFn i.sortedInputFields) (1 + 2 * s)
    (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩; exact rationalWordWidth_of_height (hFields j))
  simp only [List.length_ofFn, Nat.zero_add] at hCopy hWords
  have hPayload : rationalArrayCopyWork (List.ofFn i.sortedInputFields) 0 ≤ 72 * (1 + 2 * s) := by
    have h := hCopy.trans (Nat.mul_le_mul_left 12 hWords)
    nlinarith
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive 6
  exact Nat.add_le_add hPayload hLoop

def profileConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalNestedSpec) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  if hq0 : i.q = 0 then RationalThreeSpecCode.endpointConstructionMetadataWork primitive c (i.longInput hq0)
  else if hq1 : i.q = 1 then RationalThreeSpecCode.endpointConstructionMetadataWork primitive c (i.shortInput hq1)
  else
    let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
    sortingFieldsMetadataWork primitive i + RationalNestedInput.profileConstructionMetadataWork primitive c j K bits +
      if i.a ≤ i.d then 0 else PreparedSegmentDescriptor.preparationMetadataBitWork primitive (i.profile K bits)

def profileConstructionMetadataBound (c s K : ℕ) : ℕ :=
  RationalThreeSpecCode.endpointConstructionMetadataBound c s + sortingFieldsMetadataBound c s +
    RationalNestedInput.profileConstructionMetadataBound c s K +
      PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 45)

theorem profileConstructionMetadataBound_mono (c : ℕ) {s t K L : ℕ} (hs : s ≤ t) (hK : K ≤ L) :
    profileConstructionMetadataBound c s K ≤ profileConstructionMetadataBound c t L := by
  have hEndpoint := RationalThreeSpecCode.endpointConstructionMetadataBound_mono c hs
  have hSorting : sortingFieldsMetadataBound c s ≤ sortingFieldsMetadataBound c t := by unfold sortingFieldsMetadataBound; omega
  have hInterior := RationalNestedInput.profileConstructionMetadataBound_mono c hs hK
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 18) (expressionHeightBudget_input_mono hs 45)
  unfold profileConstructionMetadataBound
  gcongr

theorem FieldsHeight.profileConstructionMetadataWork_common {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hK : K + 2 ≤ s) (bits : Fin K → Bool) :
    profileConstructionMetadataWork primitive c i K bits ≤ profileConstructionMetadataBound c s K := by
  unfold profileConstructionMetadataWork
  split
  · rename_i hq0
    have hEndpoint := RationalThreeSpecCode.endpointConstructionMetadataWork_bound primitive c hPrimitive _ s hs (h.longInput hs hq0)
    unfold profileConstructionMetadataBound
    omega
  · split
    · rename_i hq0 hq1
      have hEndpoint := RationalThreeSpecCode.endpointConstructionMetadataWork_bound primitive c hPrimitive _ s hs (h.shortInput hs hq1)
      unfold profileConstructionMetadataBound
      omega
    · rename_i hq0 hq1
      have hSorting := h.sortingFieldsMetadataWork_bound primitive c hPrimitive
      have hInterior := (h.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)).profileConstructionMetadataWork_common
        hs primitive c hPrimitive K hK bits
      have hTable := h.profile hs K bits
      rw [max_eq_left hK] at hTable
      have hPayload := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ hTable
      dsimp only
      split <;> unfold profileConstructionMetadataBound <;> omega

theorem FieldsHeight.profileConstructionMetadataWork_bound {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    profileConstructionMetadataWork primitive c i K bits ≤ profileConstructionMetadataBound c (max s (K + 2)) K :=
  (h.mono (le_max_left _ _)).profileConstructionMetadataWork_common (hs.trans (le_max_left _ _))
    primitive c hPrimitive K (le_max_right _ _) bits

end Blotto.RationalNestedSpec
