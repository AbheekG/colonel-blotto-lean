import Blotto.RationalFourSpecConstructionMetadata
import Blotto.RationalTerminalGroupCompleteProcessing

/-! Entry construction for all two/three-group branches retains repeated
lottery preparation and start-list metadata. Four-variable runtime factories
and packed input/output routes are separate components. -/

namespace Blotto.RationalUniformGroupSpec

def entryConstructionMetadataWork {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (primitive : ℕ → ℕ) (c : ℕ) : ℕ := by
  by_cases h2 : m = 2
  · exact 4 * PreparedSegmentDescriptor.preparationMetadataBitWork primitive (i.lottery hm) +
      rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn (i.lottery hm).weight)
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact 4 * rationalEnvironmentMetadataWork primitive (RationalThreeSpecCode.environment i.threeInput) +
      2 * RationalThreeSpecCode.constructionMetadataWork primitive c i.threeInput +
        rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn (i.lottery hm).weight)

def entryConstructionMetadataBound (c s : ℕ) : ℕ :=
  4 * PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 18) +
    4 * rationalEnvironmentMetadataBound c 5 (1 + 2 * s) + 2 * RationalThreeSpecCode.constructionMetadataBound c s +
      rationalEnvironmentMetadataBound c 9 (1 + 2 * expressionHeightBudget s 18)

theorem FieldsHeight.entryConstructionMetadataWork_bound {m : ℕ} {i : RationalUniformGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    i.entryConstructionMetadataWork hm primitive c ≤ entryConstructionMetadataBound c s := by
  have hStart := rationalEnvironmentMetadataWork_bound primitive c hPrimitive
    (FixedArrayTable.ofFn (i.lottery hm).weight) (1 + 2 * expressionHeightBudget s 18)
    (fun j => by
      rw [FixedArrayTable.read_ofFn]
      exact rationalWordWidth_of_height ((h.lottery hs hm).1 j))
  rcases hm with rfl | rfl
  · have hTable := (PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _
      (h.lottery hs (Or.inl rfl))).trans (PreparedSegmentDescriptor.preparationMetadataBound_mono c
        (by decide : 2 ≤ 3) (le_refl 9) (le_refl _))
    change 4 * PreparedSegmentDescriptor.preparationMetadataBitWork primitive (i.lottery (Or.inl rfl)) +
      rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn (i.lottery (Or.inl rfl)).weight) ≤ _
    unfold entryConstructionMetadataBound
    omega
  · have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
      (fun j => rationalWordWidth_of_height (h.three_environment hs j))
    have hChild := RationalThreeSpecCode.constructionMetadataWork_bound primitive c hPrimitive i.threeInput s hs (h.three_environment hs)
    change 4 * rationalEnvironmentMetadataWork primitive (RationalThreeSpecCode.environment i.threeInput) +
      2 * RationalThreeSpecCode.constructionMetadataWork primitive c i.threeInput +
        rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn (i.lottery (Or.inr rfl)).weight) ≤ _
    unfold entryConstructionMetadataBound
    omega

end Blotto.RationalUniformGroupSpec

namespace Blotto.RationalMixedGroupSpec

def entryConstructionMetadataWork {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (primitive : ℕ → ℕ) (c : ℕ) : ℕ := by
  by_cases h2 : m = 2
  · subst m
    exact 4 * rationalEnvironmentMetadataWork primitive (RationalThreeSpecCode.environment i.threeInput) +
      2 * RationalThreeSpecCode.constructionMetadataWork primitive c i.threeInput +
        rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn i.threeInput.segmentLottery.weight)
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact RationalFourSpec.wrapperConstructionMetadataWork primitive i.fourInput +
      RationalFourInput.entryConstructionMetadataWork primitive c i.fourInput.input

def entryConstructionMetadataBound (c s : ℕ) : ℕ :=
  4 * rationalEnvironmentMetadataBound c 5 (1 + 2 * s) + 2 * RationalThreeSpecCode.constructionMetadataBound c s +
    rationalEnvironmentMetadataBound c 9 (1 + 2 * expressionHeightBudget s 18) +
      RationalFourSpec.wrapperConstructionMetadataBound c s + RationalFourInput.entryConstructionMetadataBound c s

theorem FieldsHeight.entryConstructionMetadataWork_bound {m : ℕ} {i : RationalMixedGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    i.entryConstructionMetadataWork hm primitive c ≤ entryConstructionMetadataBound c s := by
  rcases hm with rfl | rfl
  · have hEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _
      (fun j => rationalWordWidth_of_height (h.three_environment j))
    have hChild := RationalThreeSpecCode.constructionMetadataWork_bound primitive c hPrimitive i.threeInput s hs h.three_environment
    have hTable := RationalThreeSpecCode.descriptor_height i.threeInput s hs h.three_environment
    have hStart := rationalEnvironmentMetadataWork_bound primitive c hPrimitive
      (FixedArrayTable.ofFn i.threeInput.segmentLottery.weight) (1 + 2 * expressionHeightBudget s 18)
      (fun j => by
        rw [FixedArrayTable.read_ofFn]
        exact rationalWordWidth_of_height (hTable.1 j))
    change 4 * rationalEnvironmentMetadataWork primitive (RationalThreeSpecCode.environment i.threeInput) +
      2 * RationalThreeSpecCode.constructionMetadataWork primitive c i.threeInput +
        rationalEnvironmentMetadataWork primitive (FixedArrayTable.ofFn i.threeInput.segmentLottery.weight) ≤ _
    unfold entryConstructionMetadataBound
    omega
  · have hWrapper := h.fourInput.wrapperConstructionMetadataWork_bound primitive c hPrimitive
    have hEntry := h.fourInput.input.entryConstructionMetadataWork_bound hs primitive c hPrimitive
    change RationalFourSpec.wrapperConstructionMetadataWork primitive i.fourInput +
      RationalFourInput.entryConstructionMetadataWork primitive c i.fourInput.input ≤ _
    unfold entryConstructionMetadataBound
    omega

end Blotto.RationalMixedGroupSpec

namespace Blotto.RationalTerminalLotto

def entryConstructionMetadataWork {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) (c : ℕ) : ℕ :=
  let packed := RationalTerminalPacking.prepare i
  match h : i.pivot with
  | none => (packed.uniformSpec (i.pivot_none h)).entryConstructionMetadataWork i.groups_count primitive c
  | some pivot => (packed.mixedSpec pivot (i.pivot_some h)).entryConstructionMetadataWork i.groups_count primitive c

def entryConstructionMetadataBound (c s : ℕ) : ℕ :=
  RationalUniformGroupSpec.entryConstructionMetadataBound c s +
    RationalMixedGroupSpec.entryConstructionMetadataBound c (expressionHeightBudget s 1)

theorem OnLattice.entryConstructionMetadataWork_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    i.entryConstructionMetadataWork primitive c ≤ entryConstructionMetadataBound c s := by
  unfold entryConstructionMetadataWork
  dsimp only
  split
  · rename_i hNone
    rw [RationalTerminalPacking.uniformSpec_eq]
    have hp := (h.uniformSpec hD hB s hBudget hWidth (i.pivot_none hNone)).entryConstructionMetadataWork_bound
      hs i.groups_count primitive c hPrimitive
    exact hp.trans (Nat.le_add_right _ _)
  · rename_i pivot hSome
    rw [RationalTerminalPacking.mixedSpec_eq]
    have hp := (h.mixedSpec hD hB s hBudget hWidth pivot (i.pivot_some hSome)).entryConstructionMetadataWork_bound
      (hs.trans (expressionHeightBudget_ge_input s 1)) i.groups_count primitive c hPrimitive
    exact hp.trans (Nat.le_add_left _ _)

end Blotto.RationalTerminalLotto
