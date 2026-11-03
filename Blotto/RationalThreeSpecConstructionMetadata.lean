import Blotto.RationalOrderedConstructionMetadata
import Blotto.RationalNestedSpecPreparation

/-! Three-spec ordering retains separate input/ordered environments, the
ordered construction charge and selected permutation table. Endpoint wrappers
also retain their nine-slot padding. Caller/physical contracts stay separate. -/

namespace Blotto.RationalThreeSpecCode

def constructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalThreeSpec) : ℕ :=
  rationalEnvironmentMetadataWork primitive (environment i) +
    rationalEnvironmentMetadataWork primitive (RationalThreeInputCode.environment i.orderedInput) +
      RationalThreeInputCode.constructionMetadataWork primitive c i.orderedInput +
        if i.a ≤ i.d then 0 else PreparedSegmentDescriptor.preparationMetadataBitWork primitive i.segmentLottery

def constructionMetadataBound (c s : ℕ) : ℕ :=
  2 * rationalEnvironmentMetadataBound c 5 (1 + 2 * s) + RationalThreeInputCode.constructionMetadataBound c s +
    PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 18)

theorem constructionMetadataBound_mono (c : ℕ) : Monotone (constructionMetadataBound c) := by
  intro a b hab
  have hEnv := rationalEnvironmentMetadataBound_mono c (le_refl 5) (show 1 + 2 * a ≤ 1 + 2 * b by omega)
  have hChild := RationalThreeInputCode.constructionMetadataBound_mono c hab
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 9) (expressionHeightBudget_input_mono hab 18)
  unfold constructionMetadataBound
  gcongr

theorem constructionMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (i : RationalThreeSpec) (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    constructionMetadataWork primitive c i ≤ constructionMetadataBound c s := by
  have hInput := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _ (fun j => rationalWordWidth_of_height (hEnv j))
  have hOrdered := ordered_environment_height i s hEnv
  have hOrderedEnv := rationalEnvironmentMetadataWork_bound primitive c hPrimitive _ _ (fun j => rationalWordWidth_of_height (hOrdered j))
  have hChild := RationalThreeInputCode.constructionMetadataWork_bound primitive c hPrimitive _ s hs hOrdered
  have hTable := PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ (descriptor_height i s hs hEnv)
  unfold constructionMetadataWork constructionMetadataBound
  split <;> omega

def endpointConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (i : RationalThreeSpec) : ℕ :=
  constructionMetadataWork primitive c i + i.segmentLottery.paddingMetadataWork primitive 9 0

def endpointConstructionMetadataBound (c s : ℕ) : ℕ :=
  constructionMetadataBound c s + PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 18)

theorem endpointConstructionMetadataBound_mono (c : ℕ) : Monotone (endpointConstructionMetadataBound c) := by
  intro a b hab
  have hInput := constructionMetadataBound_mono c hab
  have hTable := PreparedSegmentDescriptor.preparationMetadataBound_mono c (le_refl 3) (le_refl 18) (expressionHeightBudget_input_mono hab 18)
  unfold endpointConstructionMetadataBound
  gcongr

theorem endpointConstructionMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (i : RationalThreeSpec) (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    endpointConstructionMetadataWork primitive c i ≤ endpointConstructionMetadataBound c s := by
  have hInput := constructionMetadataWork_bound primitive c hPrimitive i s hs hEnv
  have hTable := RationalSegmentLottery.paddingMetadataWork_bound primitive c hPrimitive _ 9 0 _
    (hs.trans (expressionHeightBudget_ge_input s 18)) (descriptor_height i s hs hEnv)
  change i.segmentLottery.paddingMetadataWork primitive 9 0 ≤ PreparedSegmentDescriptor.preparationMetadataBound c 3 18 (expressionHeightBudget s 18) at hTable
  exact Nat.add_le_add hInput hTable

end Blotto.RationalThreeSpecCode
