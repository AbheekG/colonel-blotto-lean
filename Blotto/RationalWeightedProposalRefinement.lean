import Blotto.RationalWeightedGuideTree

/-! The native rational recursive formulas have the exact real augmented
proposal semantics. Each formula follows one supplied record; it does not
construct a full product-state table. Sampling and guide costs remain separate. -/

namespace Blotto
open scoped BigOperators
namespace RationalWeightedGuideTree

theorem guide_resource_real (tree : RationalWeightedGuideTree) (i : Fin tree.guideSize) :
    (tree.guide.resource i : ℝ) = tree.real.guide.resource (i.cast tree.real_guideSize.symm) := by
  cases tree <;> rfl

theorem guide_mass_real (tree : RationalWeightedGuideTree) (i : Fin tree.guideSize) :
    (tree.guide.mass i : ℝ) = tree.real.guide.mass (i.cast tree.real_guideSize.symm) := by
  cases tree <;> rfl

theorem guidePrefix_real (tree : RationalWeightedGuideTree) (B : ℚ) :
    (tree.guidePrefix B : ℝ) = tree.real.guide.prefixMass (B : ℝ) := by
  cases tree with
  | leaf family guide gamma => exact guide.prefixMass_real B
  | fork guide gamma left right => exact guide.prefixMass_real B

theorem guideConvolution_real (left right : RationalWeightedGuideTree) (B : ℚ) :
    (left.guide.convolution right.guide B : ℝ) = left.real.guide.convolution right.real.guide (B : ℝ) := by
  cases left <;> cases right <;> apply RationalWeightedFamily.convolution_real

theorem resource_real (tree : RationalWeightedGuideTree) (record : tree.Record) :
    (tree.resource record : ℝ) = tree.real.proposalResource (tree.recordReal record) := by
  induction tree with
  | leaf family guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    rcases record with ⟨i, r, l⟩
    change ((left.resource l + right.resource r : ℚ) : ℝ) = _
    rw [Rat.cast_add, ihL l, ihR r]
    exact (WeightedGuideTree.proposalResource_fork guide.real (gamma : ℝ) left.real right.real
      (i.cast left.real_guideSize.symm, right.recordReal r, left.recordReal l)).symm

theorem weight_real (tree : RationalWeightedGuideTree) (record : tree.Record) :
    (tree.weight record : ℝ) = tree.real.proposalWeight (tree.recordReal record) := by
  induction tree with
  | leaf family guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    rcases record with ⟨i, r, l⟩
    change ((left.weight l * right.weight r : ℚ) : ℝ) = _
    rw [Rat.cast_mul, ihL l, ihR r]
    exact (WeightedGuideTree.proposalWeight_fork guide.real (gamma : ℝ) left.real right.real
      (i.cast left.real_guideSize.symm, right.recordReal r, left.recordReal l)).symm

theorem factor_real (tree : RationalWeightedGuideTree) : (tree.factor : ℝ) = tree.real.factor := by
  induction tree with
  | leaf family guide gamma => rfl
  | fork guide gamma left right ihL ihR => simp only [factor, real, WeightedGuideTree.factor, Rat.cast_mul, ihL, ihR]

theorem probability_real (tree : RationalWeightedGuideTree) (B : ℚ) (record : tree.Record) :
    (tree.probability B record : ℝ) = tree.real.proposalProbability (B : ℝ) (tree.recordReal record) := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    change ((if family.resource record ≤ B then family.mass record / family.prefixMass B else 0 : ℚ) : ℝ) =
      if (family.resource record : ℝ) ≤ (B : ℝ) then (family.mass record : ℝ) / family.real.prefixMass (B : ℝ) else 0
    have he : (family.resource record : ℝ) ≤ (B : ℝ) ↔ family.resource record ≤ B := by norm_cast
    simp only [he]
    split_ifs <;> simp only [Rat.cast_div, Rat.cast_zero, family.prefixMass_real]
  | fork guide gamma left right ihL ihR =>
    change (((left.guide.mass record.1 * right.guidePrefix (B - left.guide.resource record.1) /
      left.guide.convolution right.guide B) * right.probability (B - left.guide.resource record.1) record.2.1 *
        left.probability (B - right.resource record.2.1) record.2.2 : ℚ) : ℝ) = _
    simp only [real, WeightedGuideTree.proposalProbability, recordReal, WeightedResourceFamily.syntheticChoice,
      Rat.cast_mul, Rat.cast_div, guide_mass_real, guidePrefix_real, guideConvolution_real,
      ihL, ihR, Rat.cast_sub, guide_resource_real, resource_real]

theorem importance_real (tree : RationalWeightedGuideTree) (B : ℚ) (record : tree.Record) :
    (tree.importance B record : ℝ) = tree.real.proposalImportance (B : ℝ) (tree.recordReal record) := by
  induction tree generalizing B with
  | leaf family guide gamma => exact family.prefixMass_real B
  | fork guide gamma left right ihL ihR =>
    change (((left.guide.convolution right.guide B *
      left.importance (B - right.resource record.2.1) record.2.2 *
      right.importance (B - left.guide.resource record.1) record.2.1 /
      (left.guidePrefix (B - right.resource record.2.1) *
        right.guidePrefix (B - left.guide.resource record.1))) : ℚ) : ℝ) = _
    simp only [real, WeightedGuideTree.proposalImportance, recordReal, WeightedProposalStep.importance,
      Rat.cast_mul, Rat.cast_div, guidePrefix_real, guideConvolution_real, ihL, ihR,
      Rat.cast_sub, guide_resource_real, resource_real]

end RationalWeightedGuideTree
end Blotto
