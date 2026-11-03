import Blotto.PreparedDescriptorMetadataWork
import Blotto.RationalPreparedDescriptorCost

/-! The primary regular-three and overlap cached compilers now add eager
table-construction metadata to their formula/payload prices. All fixed slots
remain included. Parent/environment/producer metadata and physical backend/
address/ownership/space contracts are separate. -/

namespace Blotto.RationalThreeGeometryCode

noncomputable def preparedDescriptorWithMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ)
    (g : RationalThreeGeometry) : ℕ :=
  preparedDescriptorBitCost model g + PreparedSegmentDescriptor.preparationMetadataBitWork primitive (compiledLotteryReference g)

theorem preparedDescriptorWithMetadataWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (g : RationalThreeGeometry) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment g).read j) s) :
    preparedDescriptorWithMetadataWork model primitive g ≤ 2799 * model.rat (1 + 2 * expressionHeightBudget s 16) +
      PreparedSegmentDescriptor.preparationMetadataBound c 3 9 (expressionHeightBudget s 16) :=
  Nat.add_le_add (preparedDescriptorBitCost_bound model g s hs hEnv)
    (PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _
      (compiledLotteryReference_height g s hs hEnv))

end Blotto.RationalThreeGeometryCode
namespace Blotto.RationalOverlapFormula

noncomputable def preparedDescriptorWithMetadataWork {k h : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ)
    (G : RationalOverlapGluing k h) (B : ℚ) : ℕ :=
  preparedDescriptorBitCost model G B + PreparedSegmentDescriptor.preparationMetadataBitWork primitive (descriptorReference G B)

theorem preparedDescriptorWithMetadataWork_bound {k h : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (G : RationalOverlapGluing k h) (B : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hFirst : G.first.HeightAt s) (hSecond : G.second.HeightAt s) (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    preparedDescriptorWithMetadataWork model primitive G B ≤
      2185 * (k * h) * model.rat (1 + 2 * expressionHeightBudget s 9) +
        PreparedSegmentDescriptor.preparationMetadataBound c 4 (k * h) (expressionHeightBudget s 9) := by
  have hReference : (descriptorReference G B).HeightAt (expressionHeightBudget s 9) := by
    rw [descriptorReference_eq]
    exact (G.descriptor_height B s hs hFirst hSecond hD hB).mono (expressionHeightBudget_mono s (by decide : 6 ≤ 9))
  exact Nat.add_le_add (preparedDescriptorBitCost_bound model G B s hs hFirst hSecond hD hB)
    (PreparedSegmentDescriptor.preparationMetadataBitWork_bound primitive c hPrimitive _ _ hReference)

end Blotto.RationalOverlapFormula
