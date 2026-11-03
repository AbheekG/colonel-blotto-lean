import Blotto.PreparedImplicitSampler

/-! Original zero-resource codes construct a concrete feasible fallback for
every nonnegative budget. This is the whole zero allocation, with no supplied
label-feasibility or normalizer-positivity oracle. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree
open scoped BigOperators Classical

def ZeroResources : ProposalTree → Prop
  | .leaf data _ _ => data.decode 0 = 0
  | .fork _ _ left right => left.ZeroResources ∧ right.ZeroResources

def zeroLabel : (tree : ProposalTree) → Fin tree.projected.trueSize
  | .leaf data _ _ => ⟨0, Nat.zero_lt_succ data.cap⟩
  | .fork _ _ left right => finProdFinEquiv (left.zeroLabel, right.zeroLabel)

theorem zeroLabel_resource (tree : ProposalTree) (hz : tree.ZeroResources) :
    tree.projected.real.trueFamily.resource (tree.zeroLabel.cast tree.projected.real_trueSize.symm) = 0 := by
  induction tree with
  | leaf data guide gamma =>
    change data.decode 0 = 0 at hz
    change (data.decode 0 : ℝ) = 0
    exact_mod_cast hz
  | fork guide gamma left right ihL ihR =>
    have hLabel : ((fork guide gamma left right).zeroLabel).cast
        (fork guide gamma left right).projected.real_trueSize.symm =
      finProdFinEquiv (left.zeroLabel.cast left.projected.real_trueSize.symm,
        right.zeroLabel.cast right.projected.real_trueSize.symm) := by
      apply Fin.ext
      change (finProdFinEquiv (left.zeroLabel, right.zeroLabel)).val =
        (finProdFinEquiv (left.zeroLabel.cast left.projected.real_trueSize.symm,
          right.zeroLabel.cast right.projected.real_trueSize.symm)).val
      simp only [finProdFinEquiv_apply_val, Fin.val_cast]
      rw [right.projected.real_trueSize]
    change (left.projected.real.trueFamily.product right.projected.real.trueFamily).resource _ = 0
    rw [hLabel, WeightedResourceFamily.product_resource, ihL hz.1, ihR hz.2, zero_add]

theorem zeroLabel_feasible (tree : ProposalTree) (hz : tree.ZeroResources) (budget : ℚ) (hb : 0 ≤ budget) :
    tree.projected.real.trueFamily.resource (tree.zeroLabel.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ) := by
  rw [tree.zeroLabel_resource hz]
  exact_mod_cast hb

theorem zeroLabel_decode (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources) :
    ∀ field, tree.decodeLabel hn tree.zeroLabel field = 0 := by
  have hSum := tree.decodeLabel_resource hn tree.zeroLabel
  rw [tree.zeroLabel_resource hz] at hSum
  intro field
  have hNonneg : ∀ j, (0 : ℝ) ≤ (tree.decodeLabel hn tree.zeroLabel j : ℝ) := by
    intro j
    exact_mod_cast (tree.allocationTree hn).decode_nonnegative
      (tree.zeroLabel.cast (tree.allocationTree_labels hn).symm) j
  have hSingle := Finset.single_le_sum (fun j _ => hNonneg j) (Finset.mem_univ field)
  have he : (tree.decodeLabel hn tree.zeroLabel field : ℝ) = 0 := le_antisymm (by rw [hSum] at hSingle; exact hSingle) (hNonneg field)
  exact_mod_cast he

def zeroFallbackRow (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (budget : ℚ) (hb : 0 ≤ budget) (epsilon : ℚ)
    (bits : Fin (tree.constructed.epsilonSeedBudget epsilon) → Bool) : Fin (tree.allocationTree hn).fields → ℚ :=
  tree.constructedEpsilonRow hn budget epsilon tree.zeroLabel (tree.zeroLabel_feasible hz budget hb) bits

theorem zeroFallbackRow_contract (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (budget : ℚ) (hb : 0 ≤ budget) (epsilon : ℚ) (he : 0 < epsilon) :
    (∀ bits : Fin (tree.constructed.epsilonSeedBudget epsilon) → Bool,
      Feasible (budget : ℝ) (fun field => (tree.zeroFallbackRow hn hz budget hb epsilon bits field : ℝ))) ∧
    (∀ test : Allocation (tree.allocationTree hn).fields → ℝ, (∀ row, 0 ≤ test row ∧ test row ≤ 1) →
      |(fairBitKernel (tree.constructed.epsilonSeedBudget epsilon)).mean
        (fun bits => test (fun field => (tree.zeroFallbackRow hn hz budget hb epsilon bits field : ℝ))) -
        (tree.projected.targetKernel budget (tree.prefix_positive_of_feasible_label budget tree.zeroLabel
          (tree.zeroLabel_feasible hz budget hb))).mean (fun label => test (tree.targetAllocation hn label))| ≤ (epsilon : ℝ)) :=
  tree.constructedEpsilonRow_contract hn budget epsilon he tree.zeroLabel (tree.zeroLabel_feasible hz budget hb)

def prepareZero (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (budget : ℚ) (hb : 0 ≤ budget) : PreparedImplicitSampler :=
  PreparedImplicitSampler.prepare tree hn budget tree.zeroLabel (tree.zeroLabel_feasible hz budget hb)

end Blotto.ImplicitLeafCounts.ProposalTree
