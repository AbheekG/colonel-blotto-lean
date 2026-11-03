import Blotto.ConstructedImplicitOutput
import Blotto.ConstructedImplicitPreservation

/-! A prepared implicit sampler stores its constructed guides once. Each draw
uses only that stored tree, budget and fallback. Preparation may conservatively
enumerate child-guide pairs; repeated draws do not reconstruct access data. -/

namespace Blotto.ImplicitLeafCounts
open scoped Classical

structure PreparedImplicitSampler where
  tree : ProposalTree
  budget : ℚ
  nonnegative : tree.NonnegativeResources
  certified : tree.projected.real.LowerCertified
  fallback : Fin tree.projected.trueSize
  fallback_feasible : tree.projected.real.trueFamily.resource
    (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)

namespace PreparedImplicitSampler

def prepare (tree : ProposalTree) (hn : tree.NonnegativeResources) (budget : ℚ)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    PreparedImplicitSampler where
  tree := tree.constructed
  budget := budget
  nonnegative := tree.rebuild_nonnegativeResources hn tree.constructionGamma tree.constructionGamma_ge_one
  certified := tree.constructed_certified
  fallback := fallback.cast tree.constructed_trueSize.symm
  fallback_feasible := tree.constructed_fallback_feasible budget fallback hf

def bitBudget (prepared : PreparedImplicitSampler) (epsilon : ℚ) : ℕ := prepared.tree.epsilonSeedBudget epsilon

def drawLabel (prepared : PreparedImplicitSampler) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : Fin prepared.tree.projected.trueSize :=
  prepared.tree.epsilonOutput prepared.certified prepared.budget
    (prepared.tree.prefix_positive_of_feasible_label prepared.budget prepared.fallback prepared.fallback_feasible)
    epsilon prepared.fallback bits

def drawRow (prepared : PreparedImplicitSampler) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : Fin (prepared.tree.allocationTree prepared.nonnegative).fields → ℚ :=
  prepared.tree.decodeLabel prepared.nonnegative (prepared.drawLabel epsilon bits)

theorem prepare_drawLabel_eq (tree : ProposalTree) (hn : tree.NonnegativeResources) (budget epsilon : ℚ)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (bits : Fin (tree.constructed.epsilonSeedBudget epsilon) → Bool) :
    ((prepare tree hn budget fallback hf).drawLabel epsilon bits).cast tree.constructed_trueSize =
      tree.constructedEpsilonOutput budget epsilon fallback hf bits := rfl

theorem drawRow_contract (prepared : PreparedImplicitSampler) (epsilon : ℚ) (he : 0 < epsilon) :
    (∀ bits : Fin (prepared.bitBudget epsilon) → Bool,
      Feasible (prepared.budget : ℝ) (fun field => (prepared.drawRow epsilon bits field : ℝ))) ∧
    (∀ test : Allocation (prepared.tree.allocationTree prepared.nonnegative).fields → ℝ,
      (∀ row, 0 ≤ test row ∧ test row ≤ 1) →
      |(fairBitKernel (prepared.bitBudget epsilon)).mean
        (fun bits => test (fun field => (prepared.drawRow epsilon bits field : ℝ))) -
        (prepared.tree.projected.targetKernel prepared.budget
          (prepared.tree.prefix_positive_of_feasible_label prepared.budget prepared.fallback prepared.fallback_feasible)).mean
          (fun label => test (prepared.tree.targetAllocation prepared.nonnegative label))| ≤ (epsilon : ℝ)) := by
  have hm := prepared.tree.prefix_positive_of_feasible_label prepared.budget prepared.fallback prepared.fallback_feasible
  constructor
  · intro bits
    exact prepared.tree.epsilonRow_feasible prepared.nonnegative prepared.certified prepared.budget hm
      epsilon he prepared.fallback prepared.fallback_feasible bits
  · intro test hTest
    exact prepared.tree.epsilonRow_mean_error prepared.nonnegative prepared.certified prepared.budget hm
      epsilon he prepared.fallback prepared.fallback_feasible test hTest

end PreparedImplicitSampler
end Blotto.ImplicitLeafCounts
