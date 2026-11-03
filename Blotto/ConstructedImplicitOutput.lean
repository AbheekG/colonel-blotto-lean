import Blotto.ConstructedImplicitProposalTree
import Blotto.ImplicitPositiveTarget

/-! The actual implicit guide constructor supplies certification and preserves
the original Cartesian target. A feasible fallback derives positive target mass.
Native draws need no supplied guide or normalizer certificate. Source decoder,
full guide preparation/binary costs and original-game compiler remain separate. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree
open scoped BigOperators Classical

theorem constructed_trueSize (tree : ProposalTree) : tree.constructed.projected.trueSize = tree.projected.trueSize :=
  tree.rebuild_trueSize tree.constructionGamma tree.constructionGamma_ge_one

theorem constructed_real_trueSize (tree : ProposalTree) : tree.constructed.projected.real.trueSize = tree.projected.real.trueSize :=
  tree.rebuild_real_trueSize tree.constructionGamma tree.constructionGamma_ge_one

theorem constructed_prefix (tree : ProposalTree) (budget : ℝ) :
    tree.constructed.projected.real.trueFamily.prefixMass budget = tree.projected.real.trueFamily.prefixMass budget :=
  tree.rebuild_true_prefix tree.constructionGamma tree.constructionGamma_ge_one budget

theorem constructed_resource (tree : ProposalTree) (label : Fin tree.constructed.projected.trueSize) :
    tree.constructed.projected.real.trueFamily.resource (label.cast tree.constructed.projected.real_trueSize.symm) =
      tree.projected.real.trueFamily.resource ((label.cast tree.constructed_trueSize).cast tree.projected.real_trueSize.symm) := by
  let original := (label.cast tree.constructed_trueSize).cast tree.projected.real_trueSize.symm
  have he := (tree.rebuild_true_resource_mass tree.constructionGamma tree.constructionGamma_ge_one original).1
  change tree.constructed.projected.real.trueFamily.resource
    (original.cast tree.constructed_real_trueSize.symm) = tree.projected.real.trueFamily.resource original at he
  have hi : original.cast tree.constructed_real_trueSize.symm =
      label.cast tree.constructed.projected.real_trueSize.symm := Fin.ext rfl
  rw [hi] at he
  exact he

theorem constructed_target_mean (tree : ProposalTree) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ))
    (test : Fin tree.projected.real.trueSize → ℝ) :
    (tree.constructed.projected.targetKernel budget (by rw [tree.constructed_prefix]; exact hm)).mean
      (fun label => test (label.cast tree.constructed_real_trueSize)) =
      (tree.projected.targetKernel budget hm).mean test := by
  unfold RationalWeightedGuideTree.targetKernel
  dsimp only
  rw [tree.constructed_prefix]
  rw [← Equiv.sum_comp (finCongr tree.constructed_real_trueSize.symm)]
  apply Finset.sum_congr rfl
  intro label _
  have he := tree.rebuild_true_resource_mass tree.constructionGamma tree.constructionGamma_ge_one label
  change tree.constructed.projected.real.trueFamily.resource (label.cast tree.constructed_real_trueSize.symm) =
      tree.projected.real.trueFamily.resource label ∧
    tree.constructed.projected.real.trueFamily.mass (label.cast tree.constructed_real_trueSize.symm) =
      tree.projected.real.trueFamily.mass label at he
  simp only [finCongr_apply, WeightedGuideTree.feasibleTargetWeight, he.1, he.2, Fin.cast_cast, Fin.cast_refl, id_eq]

theorem constructed_prefix_positive (tree : ProposalTree) (budget : ℚ) (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    0 < tree.constructed.projected.real.trueFamily.prefixMass (budget : ℝ) := by
  rw [tree.constructed_prefix]
  exact tree.prefix_positive_of_feasible_label budget fallback hf

theorem constructed_fallback_feasible (tree : ProposalTree) (budget : ℚ) (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    tree.constructed.projected.real.trueFamily.resource
      ((fallback.cast tree.constructed_trueSize.symm).cast tree.constructed.projected.real_trueSize.symm) ≤ (budget : ℝ) := by
  rw [tree.constructed_resource]
  exact hf

def constructedEpsilonOutput (tree : ProposalTree) (budget : ℚ) (epsilon : ℚ)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (bits : Fin (tree.constructed.epsilonSeedBudget epsilon) → Bool) : Fin tree.projected.trueSize :=
  (tree.constructed.epsilonOutput tree.constructed_certified budget
    (tree.constructed_prefix_positive budget fallback hf) epsilon (fallback.cast tree.constructed_trueSize.symm) bits).cast
      tree.constructed_trueSize

theorem constructedEpsilonOutput_contract (tree : ProposalTree) (budget epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    (∀ bits : Fin (tree.constructed.epsilonSeedBudget epsilon) → Bool,
      tree.projected.real.trueFamily.resource
        ((tree.constructedEpsilonOutput budget epsilon fallback hf bits).cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) ∧
    (∀ test : Fin tree.projected.real.trueSize → ℝ, (∀ label, 0 ≤ test label ∧ test label ≤ 1) →
      |(fairBitKernel (tree.constructed.epsilonSeedBudget epsilon)).mean
        (fun bits => test ((tree.constructedEpsilonOutput budget epsilon fallback hf bits).cast tree.projected.real_trueSize.symm)) -
          (tree.projected.targetKernel budget (tree.prefix_positive_of_feasible_label budget fallback hf)).mean test| ≤ (epsilon : ℝ)) := by
  have hBuilt := tree.constructed.epsilonOutput_contract tree.constructed_certified budget
    (tree.constructed_prefix_positive budget fallback hf) epsilon he (fallback.cast tree.constructed_trueSize.symm)
    (tree.constructed_fallback_feasible budget fallback hf)
  constructor
  · intro bits
    have hOut := hBuilt.1 bits
    rw [tree.constructed_resource] at hOut
    exact hOut
  · intro test hTest
    have hOut := hBuilt.2 (fun label => test (label.cast tree.constructed_real_trueSize)) (fun label => hTest _)
    rw [tree.constructed_target_mean] at hOut
    exact hOut

theorem constructed_trials (tree : ProposalTree) (E : ℕ) : tree.constructed.rejectionAttempts E ≤ 2 * (E + 1) := by
  unfold rejectionAttempts rejectionScheduleAttempts
  exact Nat.mul_le_mul_right _ tree.constructed_factorCeiling

def constructedEpsilonRow (tree : ProposalTree) (hn : tree.NonnegativeResources) (budget epsilon : ℚ)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (bits : Fin (tree.constructed.epsilonSeedBudget epsilon) → Bool) : Fin (tree.allocationTree hn).fields → ℚ :=
  tree.decodeLabel hn (tree.constructedEpsilonOutput budget epsilon fallback hf bits)

theorem constructedEpsilonRow_contract (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (budget epsilon : ℚ) (he : 0 < epsilon) (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    (∀ bits : Fin (tree.constructed.epsilonSeedBudget epsilon) → Bool,
      Feasible (budget : ℝ) (fun field => (tree.constructedEpsilonRow hn budget epsilon fallback hf bits field : ℝ))) ∧
    (∀ test : Allocation (tree.allocationTree hn).fields → ℝ, (∀ row, 0 ≤ test row ∧ test row ≤ 1) →
      |(fairBitKernel (tree.constructed.epsilonSeedBudget epsilon)).mean
        (fun bits => test (fun field => (tree.constructedEpsilonRow hn budget epsilon fallback hf bits field : ℝ))) -
          (tree.projected.targetKernel budget (tree.prefix_positive_of_feasible_label budget fallback hf)).mean
            (fun label => test (tree.targetAllocation hn label))| ≤ (epsilon : ℝ)) := by
  have hc := tree.constructedEpsilonOutput_contract budget epsilon he fallback hf
  constructor
  · intro bits
    constructor
    · intro field
      change (0 : ℝ) ≤ ((tree.allocationTree hn).decode
        ((tree.constructedEpsilonOutput budget epsilon fallback hf bits).cast (tree.allocationTree_labels hn).symm) field : ℝ)
      exact_mod_cast (tree.allocationTree hn).decode_nonnegative _ field
    · rw [constructedEpsilonRow, tree.decodeLabel_resource hn]
      exact hc.1 bits
  · intro test hTest
    exact hc.2 (fun label => test (tree.targetAllocation hn label)) (fun label => hTest _)

end Blotto.ImplicitLeafCounts.ProposalTree
